/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.FourBoundary

/-!
# Subsubsection 4.4.2: at least one boundary gap has size one

Standing hypotheses: those of Subsection 4.4 (`Standing44`) and, after a dihedral symmetry,
(4.12) `ℓ = r - 1` (written `ℓ + 1 = r`).

The claims inside the proof of Lemma 4.29 are steps of a proof by contradiction: their context
(`Ctx429`) fixes `a ∈ {2, …, k-2}` and a `σ`-copy `Θ ⊆ D_a` with `Θ ≠ Σ`. The paper's proof shows
that for a suitable `a` no such `Θ` exists; the bundle without the field `ne` is satisfiable
(take `Θ = Σ`). Claim 4.36 additionally assumes the case "(UD) holds and (BD) fails" that the
paper reduces to "by rotational symmetry" (tex l.1382).
-/

open Equiv Finset

namespace LinfPermRemoval

variable {k : ℕ}

/-- **Construction 4.28.** `P_a = (a, ℓ) + t(1,1)`, `0 < t < 1` (so `P_a ⊂ H_ℓ ∩ V_a`). -/
def Pa428 (σ : Perm (Fin k)) (a : ℕ) : Set (ℝ × ℝ) := openSeg ((a : ℝ), (lv σ : ℝ)) (1, 1)

/-- **Construction 4.28.** `D_a = Σ ∪ P_L ∪ P_R ∪ P_B ∪ P_U ∪ P_a`. -/
noncomputable def D428 (σ : Perm (Fin k)) (a : ℕ) : Set (ℝ × ℝ) := D419 σ ∪ Pa428 σ a

namespace UG

variable {k : ℕ}

/-! ### 1-based accessors -/

lemma exists_fin {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) : ∃ i' : Fin k, i = i'.val + 1 :=
  ⟨⟨i - 1, by omega⟩, by simp; omega⟩

lemma sval_fin (σ : Perm (Fin k)) (i : Fin k) : sval σ (i.val + 1) = (σ i).val + 1 := by
  have h := i.isLt
  simp [sval, (by omega : 1 ≤ i.val + 1), (by omega : i.val + 1 ≤ k)]

lemma spos_fin (σ : Perm (Fin k)) (j : Fin k) : spos σ (j.val + 1) = (σ.symm j).val + 1 := by
  have h := j.isLt
  simp [spos, (by omega : 1 ≤ j.val + 1), (by omega : j.val + 1 ≤ k)]

lemma th_fin (Θ : Fin k → ℝ × ℝ) (i : Fin k) : th Θ (i.val + 1) = Θ i := by
  have h := i.isLt
  simp [th, (by omega : 1 ≤ i.val + 1), (by omega : i.val + 1 ≤ k)]

lemma thInv_fin (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) (j : Fin k) :
    thInv σ Θ (j.val + 1) = Θ (σ.symm j) := by
  have h := j.isLt
  simp [thInv, (by omega : 1 ≤ j.val + 1), (by omega : j.val + 1 ≤ k)]

lemma sval_range (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    1 ≤ sval σ i ∧ sval σ i ≤ k := by
  obtain ⟨i, rfl⟩ := exists_fin h1 h2
  rw [sval_fin]; have := (σ i).isLt; omega

lemma spos_range (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    1 ≤ spos σ j ∧ spos σ j ≤ k := by
  obtain ⟨j, rfl⟩ := exists_fin h1 h2
  rw [spos_fin]; have := (σ.symm j).isLt; omega

lemma spos_sval (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    spos σ (sval σ i) = i := by
  obtain ⟨i, rfl⟩ := exists_fin h1 h2
  rw [sval_fin, spos_fin]; simp

lemma sval_spos (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    sval σ (spos σ j) = j := by
  obtain ⟨j, rfl⟩ := exists_fin h1 h2
  rw [spos_fin, sval_fin]; simp

lemma sval_inj (σ : Perm (Fin k)) {i i' : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) (h1' : 1 ≤ i')
    (h2' : i' ≤ k) (h : sval σ i = sval σ i') : i = i' := by
  rw [← spos_sval σ h1 h2, ← spos_sval σ h1' h2', h]

lemma spos_inj (σ : Perm (Fin k)) {j j' : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) (h1' : 1 ≤ j')
    (h2' : j' ≤ k) (h : spos σ j = spos σ j') : j = j' := by
  rw [← sval_spos σ h1 h2, ← sval_spos σ h1' h2', h]

lemma thInv_eq_th (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    thInv σ Θ j = th Θ (spos σ j) := by
  obtain ⟨j, rfl⟩ := exists_fin h1 h2
  rw [thInv_fin, spos_fin, th_fin]

lemma th_eq_thInv (σ : Perm (Fin k)) (Θ : Fin k → ℝ × ℝ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    th Θ i = thInv σ Θ (sval σ i) := by
  have := sval_range σ h1 h2
  rw [thInv_eq_th σ Θ this.1 this.2, spos_sval σ h1 h2]

section Rep

variable {σ : Perm (Fin k)} {Θ : Fin k → ℝ × ℝ}

lemma th_x_lt_iff (hR : Represents σ Θ) {i i' : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) (h1' : 1 ≤ i')
    (h2' : i' ≤ k) : (th Θ i).1 < (th Θ i').1 ↔ i < i' := by
  obtain ⟨i, rfl⟩ := exists_fin h1 h2
  obtain ⟨i', rfl⟩ := exists_fin h1' h2'
  rw [th_fin, th_fin, hR.1.lt_iff_lt, Fin.lt_def]; omega

lemma th_y_lt_iff (hR : Represents σ Θ) {i i' : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) (h1' : 1 ≤ i')
    (h2' : i' ≤ k) : (th Θ i).2 < (th Θ i').2 ↔ sval σ i < sval σ i' := by
  obtain ⟨i, rfl⟩ := exists_fin h1 h2
  obtain ⟨i', rfl⟩ := exists_fin h1' h2'
  rw [th_fin, th_fin, hR.2, sval_fin, sval_fin, Fin.lt_def]; omega

lemma thInv_y_lt_iff (hR : Represents σ Θ) {j j' : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) (h1' : 1 ≤ j')
    (h2' : j' ≤ k) : (thInv σ Θ j).2 < (thInv σ Θ j').2 ↔ j < j' := by
  have a := spos_range σ h1 h2
  have b := spos_range σ h1' h2'
  rw [thInv_eq_th σ Θ h1 h2, thInv_eq_th σ Θ h1' h2', th_y_lt_iff hR a.1 a.2 b.1 b.2,
    sval_spos σ h1 h2, sval_spos σ h1' h2']

lemma thInv_x_lt_iff (hR : Represents σ Θ) {j j' : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) (h1' : 1 ≤ j')
    (h2' : j' ≤ k) : (thInv σ Θ j).1 < (thInv σ Θ j').1 ↔ spos σ j < spos σ j' := by
  have a := spos_range σ h1 h2
  have b := spos_range σ h1' h2'
  rw [thInv_eq_th σ Θ h1 h2, thInv_eq_th σ Θ h1' h2', th_x_lt_iff hR a.1 a.2 b.1 b.2]

lemma th_inj (hR : Represents σ Θ) {i i' : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) (h1' : 1 ≤ i')
    (h2' : i' ≤ k) (h : th Θ i = th Θ i') : i = i' := by
  rcases lt_trichotomy i i' with hl | hl | hl
  · have := (th_x_lt_iff hR h1 h2 h1' h2').2 hl; rw [h] at this; exact absurd this (lt_irrefl _)
  · exact hl
  · have := (th_x_lt_iff hR h1' h2' h1 h2).2 hl; rw [h] at this; exact absurd this (lt_irrefl _)

lemma th_mem {D : Set (ℝ × ℝ)} (hc : CopyIn σ Θ D) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    th Θ i ∈ D := by
  obtain ⟨i, rfl⟩ := exists_fin h1 h2
  rw [th_fin]; exact hc.2 i

lemma thInv_mem {D : Set (ℝ × ℝ)} (hc : CopyIn σ Θ D) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    thInv σ Θ j ∈ D := by
  have := spos_range σ h1 h2
  rw [thInv_eq_th σ Θ h1 h2]; exact th_mem hc this.1 this.2

end Rep

/-! ### Canonical points -/

lemma sig_eq (σ : Perm (Fin k)) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    sig σ i = ((i : ℝ), (sval σ i : ℝ)) := by
  obtain ⟨i, rfl⟩ := exists_fin h1 h2
  rw [sig, th_fin, sval_fin, canonPt]; push_cast; rfl

lemma sigInv_eq (σ : Perm (Fin k)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    sigInv σ j = ((spos σ j : ℝ), (j : ℝ)) := by
  have := spos_range σ h1 h2
  rw [sigInv, thInv_eq_th σ _ h1 h2, ← sig, sig_eq σ this.1 this.2, sval_spos σ h1 h2]

lemma mem_canon (σ : Perm (Fin k)) {p : ℝ × ℝ} :
    p ∈ canon σ ↔ ∃ i, 1 ≤ i ∧ i ≤ k ∧ p = ((i : ℝ), (sval σ i : ℝ)) := by
  constructor
  · intro hp
    simp only [canon, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    refine ⟨i.val + 1, by omega, by have := i.isLt; omega, ?_⟩
    rw [sval_fin, canonPt]; push_cast; rfl
  · rintro ⟨i, h1, h2, rfl⟩
    obtain ⟨i, rfl⟩ := exists_fin h1 h2
    simp only [canon, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨i, ?_⟩
    rw [sval_fin, canonPt]; push_cast; rfl

lemma canon_of_y (σ : Perm (Fin k)) {p : ℝ × ℝ} (hp : p ∈ canon σ) {m : ℕ}
    (hm : p.2 = (m : ℝ)) : 1 ≤ m ∧ m ≤ k ∧ p = ((spos σ m : ℝ), (m : ℝ)) := by
  obtain ⟨i, h1, h2, rfl⟩ := (mem_canon σ).1 hp
  simp only at hm
  have hsv : sval σ i = m := by exact_mod_cast hm
  have := sval_range σ h1 h2
  refine ⟨by omega, by omega, ?_⟩
  rw [← hsv, spos_sval σ h1 h2]

lemma canon_bounds (σ : Perm (Fin k)) {p : ℝ × ℝ} (hp : p ∈ canon σ) :
    1 ≤ p.1 ∧ p.1 ≤ k ∧ 1 ≤ p.2 ∧ p.2 ≤ k ∧ (∃ m : ℕ, p.1 = m) ∧ (∃ m : ℕ, p.2 = m) := by
  obtain ⟨i, h1, h2, rfl⟩ := (mem_canon σ).1 hp
  have := sval_range σ h1 h2
  simp only
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast this.1,
    by exact_mod_cast this.2, ⟨i, rfl⟩, ⟨_, rfl⟩⟩


/-! ### Basic consequences of the standing hypotheses -/

lemma facts {σ : Perm (Fin k)} (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ) :
    4 ≤ k ∧ 2 ≤ lv σ ∧ rv σ + 1 ≤ k ∧ 2 ≤ bp σ ∧ bp σ + 1 ≤ k ∧ 2 ≤ up σ ∧ up σ + 1 ≤ k ∧
      bp σ ≠ up σ ∧ spos σ (lv σ) = 1 ∧ spos σ (rv σ) = k ∧ sval σ (bp σ) = 1 ∧
      sval σ (up σ) = k := by
  have hk1 : 1 ≤ k := by
    by_contra h
    have hk : k = 0 := by omega
    apply hσ.l_ne.2
    simp [lv, sval, hk]
  have hl := sval_range σ le_rfl hk1
  have hr := sval_range σ hk1 le_rfl
  have hb := spos_range σ le_rfl hk1
  have hu := spos_range σ hk1 le_rfl
  have hl1 := hσ.l_ne
  have hr1 := hσ.r_ne
  simp only [lv, rv, bp, up] at *
  have e1 := sval_spos σ le_rfl hk1
  have e2 := sval_spos σ hk1 le_rfl
  have hb1 : spos σ 1 ≠ 1 := fun h => hl1.1 (by have := congrArg (sval σ) h; rw [e1] at this; omega)
  have hbk : spos σ 1 ≠ k := fun h => hr1.1 (by have := congrArg (sval σ) h; rw [e1] at this; omega)
  have hu1 : spos σ k ≠ 1 := fun h => hl1.2 (by have := congrArg (sval σ) h; rw [e2] at this; omega)
  have huk : spos σ k ≠ k := fun h => hr1.2 (by have := congrArg (sval σ) h; rw [e2] at this; omega)
  have hk4 : 4 ≤ k := by omega
  refine ⟨hk4, by omega, by omega, by omega, by omega, by omega, by omega, ?_,
    spos_sval σ le_rfl hk1, spos_sval σ hk1 le_rfl, e1, e2⟩
  intro h
  have := spos_inj σ le_rfl hk1 hk1 le_rfl h
  omega

/-! ### The parts of the support -/

/-- Both coordinates are non-integral. -/
def NI (p : ℝ × ℝ) : Prop := ∀ m : ℤ, p.1 ≠ m ∧ p.2 ≠ m

lemma diag_NI {p : ℝ × ℝ} (c1 c2 s1 s2 : ℤ) (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1)
    (t : ℝ) (hx : p.1 = c1 + t * s1) (hy : p.2 = c2 + t * s2) (hl : p ∉ lattice) : NI p := by
  have e1 : ((s1 : ℝ)) * s1 = 1 := by rcases hs1 with rfl | rfl <;> norm_num
  have e2 : ((s2 : ℝ)) * s2 = 1 := by rcases hs2 with rfl | rfl <;> norm_num
  intro m
  constructor
  · intro h
    apply hl
    have ht : t = (m - c1) * s1 := by
      have : t * s1 = m - c1 := by linarith
      calc t = t * ((s1 : ℝ) * s1) := by rw [e1]; ring
        _ = (m - c1) * s1 := by rw [← this]; ring
    refine ⟨m, c2 + (m - c1) * s1 * s2, Prod.ext h ?_⟩
    rw [hy, ht]; push_cast; ring
  · intro h
    apply hl
    have ht : t = (m - c2) * s2 := by
      have : t * s2 = m - c2 := by linarith
      calc t = t * ((s2 : ℝ) * s2) := by rw [e2]; ring
        _ = (m - c2) * s2 := by rw [← this]; ring
    refine ⟨c1 + (m - c2) * s2 * s1, m, Prod.ext ?_ h⟩
    rw [hx, ht]; push_cast; ring

section Parts

variable {σ : Perm (Fin k)}

lemma PL_props (hlr : lv σ < rv σ) {p : ℝ × ℝ} (hp : p ∈ PL419 σ) :
    p.1 < 1 ∧ (lv σ : ℝ) + 1 < p.2 ∧ p.2 ≤ k ∧ NI p ∧
      (lv σ < sval σ 2 → p.1 + p.2 = 2) ∧ (¬ lv σ < sval σ 2 → p.2 - p.1 = k - 1) := by
  obtain ⟨⟨hI, hlat⟩, htr⟩ := hp
  simp only [hlr, ↓reduceIte] at htr
  unfold IL419 closedSeg at hI
  split_ifs at hI with h2
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hni := diag_NI 1 1 (-1) 1 (by norm_num) (by norm_num) t (by push_cast; ring)
      (by push_cast; ring) hlat
    have h1 := (hni 1).1
    simp only [Int.cast_one] at h1
    have ht : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; simp at h1)
    refine ⟨by dsimp only; linarith, htr, by dsimp only; linarith, hni,
      fun _ => by dsimp only; ring,
      fun h => absurd h2 h⟩
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hni := diag_NI 1 k (-1) (-1) (by norm_num) (by norm_num) t (by push_cast; ring)
      (by push_cast; ring) hlat
    have h1 := (hni 1).1
    simp only [Int.cast_one] at h1
    have ht : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; simp at h1)
    refine ⟨by dsimp only; linarith, htr, by dsimp only; linarith, hni, fun h => absurd h h2,
      fun _ => by dsimp only; ring⟩

lemma PR_props (hlr : lv σ < rv σ) {p : ℝ × ℝ} (hp : p ∈ PR419 σ) :
    (k : ℝ) < p.1 ∧ p.2 < (rv σ : ℝ) - 1 ∧ 1 ≤ p.2 ∧ NI p ∧
      (rv σ < sval σ (k - 1) → p.2 - p.1 = 1 - k) ∧
      (¬ rv σ < sval σ (k - 1) → p.1 + p.2 = 2 * k) := by
  obtain ⟨⟨hI, hlat⟩, htr⟩ := hp
  simp only [hlr, ↓reduceIte] at htr
  unfold IR419 closedSeg at hI
  split_ifs at hI with h2
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hni := diag_NI k 1 1 1 (by norm_num) (by norm_num) t (by push_cast; ring)
      (by push_cast; ring) hlat
    have h1 := (hni k).1
    simp only [Int.cast_natCast] at h1
    have ht : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; simp at h1)
    refine ⟨by dsimp only; linarith, htr, by dsimp only; linarith, hni,
      fun _ => by dsimp only; ring,
      fun h => absurd h2 h⟩
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hni := diag_NI k k 1 (-1) (by norm_num) (by norm_num) t (by push_cast; ring)
      (by push_cast; ring) hlat
    have h1 := (hni k).1
    simp only [Int.cast_natCast] at h1
    have ht : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; simp at h1)
    refine ⟨by dsimp only; linarith, htr, by dsimp only; linarith, hni, fun h => absurd h h2,
      fun _ => by dsimp only; ring⟩

lemma PB_props {p : ℝ × ℝ} (hp : p ∈ PB419 σ) :
    p.2 < 1 ∧ 1 ≤ p.1 ∧ p.1 ≤ k ∧ NI p ∧
      (bp σ < up σ → (bp σ : ℝ) + 1 < p.1) ∧ (¬ bp σ < up σ → p.1 < (bp σ : ℝ) - 1) ∧
      (bp σ < spos σ 2 → p.1 + p.2 = 2) ∧ (¬ bp σ < spos σ 2 → p.1 - p.2 = k - 1) := by
  obtain ⟨⟨hI, hlat⟩, htr⟩ := hp
  have htr1 : bp σ < up σ → (bp σ : ℝ) + 1 < p.1 := fun h => by
    simp only [h, ↓reduceIte] at htr; exact htr
  have htr2 : ¬ bp σ < up σ → p.1 < (bp σ : ℝ) - 1 := fun h => by
    simp only [h, ↓reduceIte] at htr; exact htr
  unfold IB419 closedSeg at hI
  split_ifs at hI with h2
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hni := diag_NI 1 1 1 (-1) (by norm_num) (by norm_num) t (by push_cast; ring)
      (by push_cast; ring) hlat
    have h1 := (hni 1).1
    simp only [Int.cast_one] at h1
    have ht : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; simp at h1)
    refine ⟨by dsimp only; linarith, by dsimp only; linarith, by dsimp only; linarith, hni,
      htr1, htr2,
      fun _ => by dsimp only; ring, fun h => absurd h2 h⟩
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hni := diag_NI k 1 (-1) (-1) (by norm_num) (by norm_num) t (by push_cast; ring)
      (by push_cast; ring) hlat
    have h1 := (hni 1).2
    simp only [Int.cast_one] at h1
    have ht : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; simp at h1)
    refine ⟨by dsimp only; linarith, by dsimp only; linarith, by dsimp only; linarith, hni,
      htr1, htr2,
      fun h => absurd h h2, fun _ => by dsimp only; ring⟩

lemma PU_props {p : ℝ × ℝ} (hp : p ∈ PU419 σ) :
    (k : ℝ) < p.2 ∧ 1 ≤ p.1 ∧ p.1 ≤ k ∧ NI p ∧
      (bp σ < up σ → p.1 < (up σ : ℝ) - 1) ∧ (¬ bp σ < up σ → (up σ : ℝ) + 1 < p.1) ∧
      (up σ < spos σ (k - 1) → p.2 - p.1 = k - 1) ∧
      (¬ up σ < spos σ (k - 1) → p.1 + p.2 = 2 * k) := by
  obtain ⟨⟨hI, hlat⟩, htr⟩ := hp
  have htr1 : bp σ < up σ → p.1 < (up σ : ℝ) - 1 := fun h => by
    simp only [h, ↓reduceIte] at htr; exact htr
  have htr2 : ¬ bp σ < up σ → (up σ : ℝ) + 1 < p.1 := fun h => by
    simp only [h, ↓reduceIte] at htr; exact htr
  unfold IU419 closedSeg at hI
  split_ifs at hI with h2
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hni := diag_NI 1 k 1 1 (by norm_num) (by norm_num) t (by push_cast; ring)
      (by push_cast; ring) hlat
    have h1 := (hni 1).1
    simp only [Int.cast_one] at h1
    have ht : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; simp at h1)
    refine ⟨by dsimp only; linarith, by dsimp only; linarith, by dsimp only; linarith, hni,
      htr1, htr2,
      fun _ => by dsimp only; ring, fun h => absurd h2 h⟩
  · obtain ⟨t, ht0, htT, rfl⟩ := hI
    have hni := diag_NI k k (-1) 1 (by norm_num) (by norm_num) t (by push_cast; ring)
      (by push_cast; ring) hlat
    have h1 := (hni k).1
    simp only [Int.cast_natCast] at h1
    have ht : 0 < t := lt_of_le_of_ne ht0 (by rintro rfl; simp at h1)
    refine ⟨by dsimp only; linarith, by dsimp only; linarith, by dsimp only; linarith, hni,
      htr1, htr2,
      fun h => absurd h h2, fun _ => by dsimp only; ring⟩

lemma Pa_props {a : ℕ} {p : ℝ × ℝ} (hp : p ∈ Pa428 σ a) :
    (a : ℝ) < p.1 ∧ p.1 < a + 1 ∧ (lv σ : ℝ) < p.2 ∧ p.2 < lv σ + 1 ∧
      p.2 - p.1 = lv σ - a := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hp
  simp only
  refine ⟨by linarith, by linarith, by linarith, by linarith, by ring⟩

lemma mem_D428 {a : ℕ} {p : ℝ × ℝ} :
    p ∈ D428 σ a ↔ p ∈ canon σ ∨ p ∈ PL419 σ ∨ p ∈ PR419 σ ∨ p ∈ PB419 σ ∨ p ∈ PU419 σ ∨
      p ∈ Pa428 σ a := by
  simp only [D428, D419, Set.mem_union, Finset.mem_coe]
  tauto

lemma mem_D419 {p : ℝ × ℝ} :
    p ∈ D419 σ ↔ p ∈ canon σ ∨ p ∈ PL419 σ ∨ p ∈ PR419 σ ∨ p ∈ PB419 σ ∨ p ∈ PU419 σ := by
  simp only [D419, Set.mem_union, Finset.mem_coe]
  tauto

end Parts


/-! ### Slopes and permutation point sets -/

lemma negSlope_of {S : Set (ℝ × ℝ)} (c : ℝ) (h : ∀ p ∈ S, p.1 + p.2 = c) : NegSlope S := by
  intro p hp q hq _
  have h1 := h p hp; have h2 := h q hq
  constructor <;> intro <;> linarith

lemma posSlope_of {S : Set (ℝ × ℝ)} (c : ℝ) (h : ∀ p ∈ S, p.2 - p.1 = c) : PosSlope S := by
  intro p hp q hq _
  have h1 := h p hp; have h2 := h q hq
  constructor <;> intro <;> linarith

lemma posSlope_of' {S : Set (ℝ × ℝ)} (c : ℝ) (h : ∀ p ∈ S, p.1 - p.2 = c) : PosSlope S :=
  posSlope_of (-c) fun p hp => by have := h p hp; linarith

/-- A finite point set with pairwise distinct `x`- and `y`-coordinates is associated with a
permutation. -/
lemma isPermPointSet_of (S : Finset (ℝ × ℝ)) (hx : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → p = q)
    (hy : ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q) : IsPermPointSet S := by
  classical
  set n := S.card with hn
  have hXc : (S.image Prod.fst).card = n :=
    Finset.card_image_of_injOn fun p hp q hq h => hx p hp q hq h
  have hYc : (S.image Prod.snd).card = n :=
    Finset.card_image_of_injOn fun p hp q hq h => hy p hp q hq h
  have hmem : ∀ i : Fin n, ∃ p ∈ S, p.1 = (S.image Prod.fst).orderEmbOfFin hXc i := fun i =>
    Finset.mem_image.1 ((S.image Prod.fst).orderEmbOfFin_mem hXc i)
  choose Θ hΘS hΘx using hmem
  have hΘmono : StrictMono fun i => (Θ i).1 := by
    intro i j hij
    simp only [hΘx]
    exact ((S.image Prod.fst).orderEmbOfFin hXc).strictMono hij
  have hΘinj : Function.Injective Θ := by
    intro i j h
    exact hΘmono.injective (by simp only [h])
  let r : Fin n → Fin n := fun i =>
    ((S.image Prod.snd).orderIsoOfFin hYc).symm
      ⟨(Θ i).2, Finset.mem_image_of_mem _ (hΘS i)⟩
  have hr : ∀ i j, r i < r j ↔ (Θ i).2 < (Θ j).2 := by
    intro i j
    simp only [r, OrderIso.lt_iff_lt]
    rfl
  have hrinj : Function.Injective r := by
    intro i j h
    have h' : (Θ i).2 = (Θ j).2 := by
      have := congrArg (fun x => ((S.image Prod.snd).orderIsoOfFin hYc x : ℝ)) h
      simpa [r] using this
    exact hΘinj (hy _ (hΘS i) _ (hΘS j) h')
  let π : Perm (Fin n) := Equiv.ofBijective r (Finite.injective_iff_bijective.1 hrinj)
  refine ⟨π, Θ, ⟨hΘmono, fun i j => (hr i j).symm⟩, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact hΘS i
  · rw [Finset.card_image_of_injective _ hΘinj, Finset.card_univ, Fintype.card_fin]

section Parts2

variable {σ : Perm (Fin k)}

lemma canon_x_inj {p q : ℝ × ℝ} (hp : p ∈ canon σ) (hq : q ∈ canon σ) (h : p.1 = q.1) :
    p = q := by
  obtain ⟨i, h1, h2, rfl⟩ := (mem_canon σ).1 hp
  obtain ⟨j, h1', h2', rfl⟩ := (mem_canon σ).1 hq
  simp only at h
  have : i = j := by exact_mod_cast h
  subst this; rfl

lemma canon_y_inj {p q : ℝ × ℝ} (hp : p ∈ canon σ) (hq : q ∈ canon σ) (h : p.2 = q.2) :
    p = q := by
  obtain ⟨i, h1, h2, rfl⟩ := (mem_canon σ).1 hp
  obtain ⟨j, h1', h2', rfl⟩ := (mem_canon σ).1 hq
  simp only at h
  have h' : sval σ i = sval σ j := by exact_mod_cast h
  have : i = j := sval_inj σ h1 h2 h1' h2' h'
  subst this; rfl

lemma D419_canon_or_NI (hlr : lv σ < rv σ) {p : ℝ × ℝ} (hp : p ∈ D419 σ) :
    p ∈ canon σ ∨ NI p := by
  rcases mem_D419.1 hp with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (PL_props hlr h).2.2.2.1
  · exact Or.inr (PR_props hlr h).2.2.2.1
  · exact Or.inr (PB_props h).2.2.2.1
  · exact Or.inr (PU_props h).2.2.2.1

lemma canon_subset_D419 : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ D419 σ := fun _ hp =>
  mem_D419.2 (Or.inl hp)

lemma canon_subset_D428 (a : ℕ) : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ D428 σ a := fun _ hp =>
  mem_D428.2 (Or.inl hp)

/-- Application of Lemma 4.20: a `σ`-copy inside `D419` is `Σ`. -/
lemma copy_D419_eq (hσ : Standing44 σ) (hlr : lv σ < rv σ) {Θ : Fin k → ℝ × ℝ}
    (hc : CopyIn σ Θ (D419 σ)) : Finset.univ.image Θ = canon σ := by
  classical
  set S := Finset.univ.image Θ ∪ canon σ with hS
  have hmem : ∀ p ∈ S, (∃ i, p = Θ i) ∨ p ∈ canon σ := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h; exact Or.inl ⟨i, rfl⟩
    · exact Or.inr h
  have hinjx : Function.Injective fun i => (Θ i).1 := hc.1.1.injective
  have hinjy : ∀ i j, (Θ i).2 = (Θ j).2 → i = j := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne ((σ.injective.ne hne)) with h' | h'
    · have := (hc.1.2 i j).2 h'; rw [h] at this; exact lt_irrefl _ this
    · have := (hc.1.2 j i).2 h'; rw [h] at this; exact lt_irrefl _ this
  have hmix1 : ∀ i, ∀ q ∈ canon σ, (Θ i).1 = q.1 → Θ i = q := by
    intro i q hq h
    rcases D419_canon_or_NI hlr (hc.2 i) with h' | h'
    · exact canon_x_inj h' hq h
    · obtain ⟨m, hm⟩ := (canon_bounds σ hq).2.2.2.2.1
      exact absurd (by rw [h, hm]; simp) (h' m).1
  have hmix2 : ∀ i, ∀ q ∈ canon σ, (Θ i).2 = q.2 → Θ i = q := by
    intro i q hq h
    rcases D419_canon_or_NI hlr (hc.2 i) with h' | h'
    · exact canon_y_inj h' hq h
    · obtain ⟨m, hm⟩ := (canon_bounds σ hq).2.2.2.2.2
      exact absurd (by rw [h, hm]; simp) (h' m).2
  have hperm : IsPermPointSet S := by
    apply isPermPointSet_of
    · intro p hp q hq h
      rcases hmem p hp with ⟨i, rfl⟩ | hp' <;> rcases hmem q hq with ⟨j, rfl⟩ | hq'
      · rw [hinjx h]
      · exact hmix1 i q hq' h
      · exact (hmix1 j p hp' h.symm).symm
      · exact canon_x_inj hp' hq' h
    · intro p hp q hq h
      rcases hmem p hp with ⟨i, rfl⟩ | hp' <;> rcases hmem q hq with ⟨j, rfl⟩ | hq'
      · rw [hinjy i j h]
      · exact hmix2 i q hq' h
      · exact (hmix2 j p hp' h.symm).symm
      · exact canon_y_inj hp' hq' h
  have hsub1 : (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑S := by
    intro p hp; exact Finset.mem_coe.2 (Finset.mem_union_right _ hp)
  have hsub2 : (↑S : Set (ℝ × ℝ)) ⊆ D419 σ := by
    intro p hp
    rcases hmem p hp with ⟨i, rfl⟩ | hp'
    · exact hc.2 i
    · exact canon_subset_D419 hp'
  have hU := lemma_4_20 σ hσ S hperm hsub1 hsub2
  exact hU.2 Θ ⟨hc.1, fun i => Finset.mem_coe.2
    (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩

end Parts2


/-! ### Inductions on bounded ranges -/

lemma up_ind (P : ℕ → Prop) {j m : ℕ} (h0 : P j) (hs : ∀ s, j ≤ s → s < m → P s → P (s + 1)) :
    ∀ s, j ≤ s → s ≤ m → P s := by
  intro s hjs
  induction s, hjs using Nat.le_induction with
  | base => intro _; exact h0
  | succ s hjs ih => intro hsm; exact hs s hjs (by omega) (ih (by omega))

lemma down_ind (P : ℕ → Prop) {j : ℕ} (h0 : P j) (hs : ∀ s, 1 < s → s ≤ j → P s → P (s - 1)) :
    ∀ s, 1 ≤ s → s ≤ j → P s := by
  have key : ∀ d s, 1 ≤ s → s + d = j → P s := by
    intro d
    induction d with
    | zero => intro s _ h; rw [show s = j by omega]; exact h0
    | succ d ih =>
      intro s hs1 h
      have := hs (s + 1) (by omega) (by omega) (ih (s + 1) (by omega) (by omega))
      simpa using this
  intro s hs1 hsj
  exact key (j - s) s hs1 (by omega)

/-! ### The auxiliary context of the proof of Lemma 4.29 -/

/-- The context of the proof of Lemma 4.29 without the field `ne` (`Ctx429` minus `Θ ≠ Σ`):
standing hypotheses, `ℓ + 1 = r`, `a ∈ {2, …, k-2}`, and a `σ`-copy `Θ ⊆ D_a`. -/
structure C (σ : Perm (Fin k)) (a : ℕ) (Θ : Fin k → ℝ × ℝ) : Prop where
  standing : Standing44 σ
  lr : lv σ + 1 = rv σ
  ha : 2 ≤ a ∧ a ≤ k - 2
  copy : CopyIn σ Θ (D428 σ a)

section Ctx

variable {σ : Perm (Fin k)} {a : ℕ} {Θ : Fin k → ℝ × ℝ}

lemma C.lt (hc : C σ a Θ) : lv σ < rv σ := by have := hc.lr; omega

lemma casts_of (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ) (ha : 2 ≤ a ∧ a ≤ k - 2) :
    (rv σ : ℝ) = lv σ + 1 ∧ (2 : ℝ) ≤ lv σ ∧ (lv σ : ℝ) + 2 ≤ k ∧ (2 : ℝ) ≤ a ∧
      (a : ℝ) + 2 ≤ k ∧ (2 : ℝ) ≤ bp σ ∧ (bp σ : ℝ) + 1 ≤ k ∧ (2 : ℝ) ≤ up σ ∧
      (up σ : ℝ) + 1 ≤ k := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, -⟩ := facts hσ hlr
  refine ⟨by rw [← hlr]; push_cast; ring, by exact_mod_cast hl2, ?_, by exact_mod_cast ha.1,
    ?_, by exact_mod_cast hb2, by exact_mod_cast hbk, by exact_mod_cast hu2,
    by exact_mod_cast huk⟩
  · have : lv σ + 2 ≤ k := by omega
    exact_mod_cast this
  · have : a + 2 ≤ k := by omega
    exact_mod_cast this

lemma C.casts (hc : C σ a Θ) :
    (rv σ : ℝ) = lv σ + 1 ∧ (2 : ℝ) ≤ lv σ ∧ (lv σ : ℝ) + 2 ≤ k ∧ (2 : ℝ) ≤ a ∧
      (a : ℝ) + 2 ≤ k ∧ (2 : ℝ) ≤ bp σ ∧ (bp σ : ℝ) + 1 ≤ k ∧ (2 : ℝ) ≤ up σ ∧
      (up σ : ℝ) + 1 ≤ k :=
  casts_of hc.standing hc.lr hc.ha

/-- The consequences of `ℓ + 1 = r` alone (without the standing hypotheses): `2 ≤ k`,
`1 ≤ ℓ` and `r ≤ k`. -/
lemma lr_facts (hlr : lv σ + 1 = rv σ) : 2 ≤ k ∧ 1 ≤ lv σ ∧ rv σ ≤ k := by
  have hk2 : 2 ≤ k := by
    by_contra h
    rcases (by omega : k = 0 ∨ k = 1) with h0 | h0
    · subst h0; simp [lv, rv, sval] at hlr
    · subst h0; simp [lv, rv] at hlr
  have hl := sval_range σ le_rfl (by omega : 1 ≤ k)
  have hr := sval_range σ (by omega : 1 ≤ k) le_rfl
  exact ⟨hk2, hl.1, hr.2⟩

lemma band_Pa (hlr : lv σ + 1 = rv σ)
    {p : ℝ × ℝ} (hp : p ∈ D428 σ a) (h1 : (lv σ : ℝ) < p.2)
    (h2 : p.2 < lv σ + 1) : p ∈ Pa428 σ a := by
  obtain ⟨hk2, hl1, hrk⟩ := lr_facts hlr
  have hl1' : (1 : ℝ) ≤ lv σ := by exact_mod_cast hl1
  have hlk : (lv σ : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : lv σ + 1 ≤ k)
  have hrl : (rv σ : ℝ) = lv σ + 1 := by rw [← hlr]; push_cast; ring
  rcases mem_D428.1 hp with h | h | h | h | h | h
  · obtain ⟨m, hm⟩ := (canon_bounds σ h).2.2.2.2.2
    rw [hm] at h1 h2
    have e1 : lv σ < m := by exact_mod_cast h1
    have e2 : m < lv σ + 1 := by exact_mod_cast h2
    omega
  · have := (PL_props (by omega : lv σ < rv σ) h).2.1; linarith
  · have := (PR_props (by omega : lv σ < rv σ) h).2.1; linarith
  · have := (PB_props h).1; linarith
  · have := (PU_props h).1; linarith
  · exact h

lemma band_U (hlr : lv σ + 1 = rv σ)
    {p : ℝ × ℝ} (hp : p ∈ D428 σ a) (h : (k : ℝ) < p.2) :
    p ∈ PU419 σ := by
  obtain ⟨hk2, hl1, hrk⟩ := lr_facts hlr
  have hlk : (lv σ : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : lv σ + 1 ≤ k)
  have hrl : (rv σ : ℝ) = lv σ + 1 := by rw [← hlr]; push_cast; ring
  rcases mem_D428.1 hp with h' | h' | h' | h' | h' | h'
  · have := (canon_bounds σ h').2.2.2.1; linarith
  · have := (PL_props (by omega : lv σ < rv σ) h').2.2.1; linarith
  · have := (PR_props (by omega : lv σ < rv σ) h').2.1; linarith
  · have := (PB_props h').1
    have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  · exact h'
  · have := (Pa_props h').2.2.2.1; linarith

lemma band_B (hlr : lv σ + 1 = rv σ) {p : ℝ × ℝ} (hp : p ∈ D428 σ a) (h : p.2 < 1) :
    p ∈ PB419 σ := by
  obtain ⟨hk2, hl1, hrk⟩ := lr_facts hlr
  have hl1' : (1 : ℝ) ≤ lv σ := by exact_mod_cast hl1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hlt : lv σ < rv σ := by omega
  rcases mem_D428.1 hp with h' | h' | h' | h' | h' | h'
  · have := (canon_bounds σ h').2.2.1; linarith
  · have := (PL_props hlt h').2.1; linarith
  · have := (PR_props hlt h').2.2.1; linarith
  · exact h'
  · have := (PU_props h').1; linarith
  · have := (Pa_props h').2.2.1; linarith

lemma band_L (hlr : lv σ + 1 = rv σ) (ha : 2 ≤ a ∧ a ≤ k - 2) {p : ℝ × ℝ}
    (hp : p ∈ D428 σ a) (h : p.1 < 1) : p ∈ PL419 σ := by
  obtain ⟨hk2, hl1, hrk⟩ := lr_facts hlr
  have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast ha.1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hlt : lv σ < rv σ := by omega
  rcases mem_D428.1 hp with h' | h' | h' | h' | h' | h'
  · have := (canon_bounds σ h').1; linarith
  · exact h'
  · have := (PR_props hlt h').1; linarith
  · have := (PB_props h').2.1; linarith
  · have := (PU_props h').2.1; linarith
  · have := (Pa_props h').1; linarith

lemma band_R (hlr : lv σ + 1 = rv σ) (ha : 2 ≤ a ∧ a ≤ k - 2)
    {p : ℝ × ℝ} (hp : p ∈ D428 σ a) (h : (k : ℝ) < p.1) :
    p ∈ PR419 σ := by
  obtain ⟨hk2, hl1, hrk⟩ := lr_facts hlr
  have hak : (a : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : a + 1 ≤ k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  rcases mem_D428.1 hp with h' | h' | h' | h' | h' | h'
  · have := (canon_bounds σ h').2.1; linarith
  · have := (PL_props (by omega : lv σ < rv σ) h').1; linarith
  · exact h'
  · have := (PB_props h').2.2.1; linarith
  · have := (PU_props h').2.2.1; linarith
  · have := (Pa_props h').2.1; linarith

/-- The boundary restrictions (4.4) in `D_a`, from Claim 4.3. -/
lemma restr (hc : C σ a Θ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ k) :
    (th Θ i ∈ PL419 σ → i = 1) ∧ (th Θ i ∈ PR419 σ → i = k) ∧
      (th Θ i ∈ PB419 σ → i = bp σ) ∧ (th Θ i ∈ PU419 σ → i = up σ) := by
  obtain ⟨hk4, -⟩ := facts hc.standing hc.lr
  have hR := hc.copy.1
  have hk2 : 2 ≤ k := by omega
  have hD := canon_subset_D428 (σ := σ) a
  obtain ⟨i, rfl⟩ := exists_fin h1 h2
  rw [th_fin]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have H := claim_4_3_1 σ hk2 (D428 σ a) hD Θ hc.copy
      ⟨fun hs => negSlope_of 2 fun p hp =>
          (PL_props hc.lt (band_L hc.lr hc.ha hp.1 hp.2)).2.2.2.2.1 hs,
       fun hs => posSlope_of ((k : ℝ) - 1) fun p hp =>
        (PL_props hc.lt (band_L hc.lr hc.ha hp.1 hp.2)).2.2.2.2.2 (by unfold lv; omega)⟩
    have := H i ⟨hc.copy.2 i, (PL_props hc.lt h).1⟩
    rw [← th_fin Θ i] at this
    exact th_inj hR (by omega) h2 le_rfl (by omega) this
  · have H := claim_4_3_2 σ hk2 (D428 σ a) hD Θ hc.copy
      ⟨fun hs => negSlope_of (2 * k) fun p hp =>
          (PR_props hc.lt (band_R hc.lr hc.ha hp.1 hp.2)).2.2.2.2.2
            (by unfold rv; omega),
       fun hs => posSlope_of (1 - (k : ℝ)) fun p hp =>
        (PR_props hc.lt (band_R hc.lr hc.ha hp.1 hp.2)).2.2.2.2.1 (by unfold rv; omega)⟩
    have := H i ⟨hc.copy.2 i, (PR_props hc.lt h).1⟩
    rw [← th_fin Θ i] at this
    exact th_inj hR (by omega) h2 (by omega) le_rfl this
  · have H := claim_4_3_3 σ hk2 (D428 σ a) hD Θ hc.copy
      ⟨fun hs => negSlope_of 2 fun p hp => (PB_props (band_B hc.lr hp.1 hp.2)).2.2.2.2.2.2.1 hs,
       fun hs => posSlope_of' ((k : ℝ) - 1) fun p hp =>
        (PB_props (band_B hc.lr hp.1 hp.2)).2.2.2.2.2.2.2 (by unfold bp; omega)⟩
    have := H i ⟨hc.copy.2 i, (PB_props h).1⟩
    rw [← th_fin Θ i, thInv_eq_th σ Θ le_rfl (by omega)] at this
    have hb := spos_range σ le_rfl (by omega : 1 ≤ k)
    exact th_inj hR (by omega) h2 hb.1 hb.2 this
  · have H := claim_4_3_4 σ hk2 (D428 σ a) hD Θ hc.copy
      ⟨fun hs => negSlope_of (2 * k) fun p hp =>
          (PU_props (band_U hc.lr hp.1 hp.2)).2.2.2.2.2.2.2 (by unfold up; omega),
       fun hs => posSlope_of ((k : ℝ) - 1) fun p hp =>
        (PU_props (band_U hc.lr hp.1 hp.2)).2.2.2.2.2.2.1 (by unfold up; omega)⟩
    have := H i ⟨hc.copy.2 i, (PU_props h).1⟩
    rw [← th_fin Θ i, thInv_eq_th σ Θ (by omega) le_rfl] at this
    have hu := spos_range σ (by omega : 1 ≤ k) le_rfl
    exact th_inj hR (by omega) h2 hu.1 hu.2 this

/-- The boundary restrictions (4.4) in terms of value-ranks. -/
lemma restrInv (hc : C σ a Θ) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    (thInv σ Θ j ∈ PL419 σ → j = lv σ) ∧ (thInv σ Θ j ∈ PR419 σ → j = rv σ) ∧
      (thInv σ Θ j ∈ PB419 σ → j = 1) ∧ (thInv σ Θ j ∈ PU419 σ → j = k) := by
  obtain ⟨hk4, -⟩ := facts hc.standing hc.lr
  have hs := spos_range σ h1 h2
  have R := restr hc hs.1 hs.2
  rw [thInv_eq_th σ Θ h1 h2]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := R.1 h; rw [← sval_spos σ h1 h2, this]; rfl
  · have := R.2.1 h; rw [← sval_spos σ h1 h2, this]; rfl
  · exact spos_inj σ h1 h2 le_rfl (by omega) (R.2.2.1 h)
  · exact spos_inj σ h1 h2 (by omega) le_rfl (R.2.2.2 h)


/-! ### Claim 4.30 and Corollary 4.31 in the auxiliary context -/

lemma c430_1 (hc : C σ a Θ) : ∀ j : ℕ, 1 ≤ j → j < k → thInv σ Θ j ∉ Pa428 σ a →
    (j : ℝ) < (thInv σ Θ j).2 → ((j : ℝ) + 1) < (thInv σ Θ (j + 1)).2 := by
  intro j hj1 hjk hnP hy
  have hR := hc.copy.1
  have hlt := (thInv_y_lt_iff hR hj1 hjk.le (by omega : 1 ≤ j + 1) hjk).2 (by omega)
  have R := restrInv hc hj1 hjk.le
  suffices h : (j : ℝ) + 1 ≤ (thInv σ Θ j).2 by linarith
  rcases mem_D428.1 (thInv_mem hc.copy hj1 hjk.le) with h | h | h | h | h | h
  · obtain ⟨m, hm⟩ := (canon_bounds σ h).2.2.2.2.2
    rw [hm] at hy ⊢
    have : j < m := by exact_mod_cast hy
    have : j + 1 ≤ m := this
    exact_mod_cast this
  · have := R.1 h; subst this; exact (PL_props hc.lt h).2.1.le
  · have := R.2.1 h; subst this; have := (PR_props hc.lt h).2.1; linarith
  · have := (PB_props h).1; have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    linarith
  · have := R.2.2.2 h; omega
  · exact absurd h hnP

lemma c430_2 (hc : C σ a Θ) : ∀ j : ℕ, 1 < j → j ≤ k → thInv σ Θ j ∉ Pa428 σ a →
    (thInv σ Θ j).2 < (j : ℝ) → (thInv σ Θ (j - 1)).2 < (j : ℝ) - 1 := by
  intro j hj1 hjk hnP hy
  have hR := hc.copy.1
  have hlt := (thInv_y_lt_iff hR (by omega : 1 ≤ j - 1) (by omega) (by omega) hjk).2
    (by omega : j - 1 < j)
  have R := restrInv hc (by omega) hjk
  suffices h : (thInv σ Θ j).2 ≤ (j : ℝ) - 1 by linarith
  rcases mem_D428.1 (thInv_mem hc.copy (by omega) hjk) with h | h | h | h | h | h
  · obtain ⟨m, hm⟩ := (canon_bounds σ h).2.2.2.2.2
    rw [hm] at hy ⊢
    have : m < j := by exact_mod_cast hy
    have : m + 1 ≤ j := this
    have : (m : ℝ) + 1 ≤ j := by exact_mod_cast this
    linarith
  · have := R.1 h; subst this; have := (PL_props hc.lt h).2.1; linarith
  · have := R.2.1 h; subst this; exact (PR_props hc.lt h).2.1.le
  · have := R.2.2.1 h; omega
  · have := (PU_props h).1; have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    linarith
  · exact absurd h hnP

lemma c430_3 (hc : C σ a Θ) : ∀ i : ℕ, 1 ≤ i → i < k → th Θ i ∉ Pa428 σ a →
    (i : ℝ) < (th Θ i).1 → ((i : ℝ) + 1) < (th Θ (i + 1)).1 := by
  intro i hi1 hik hnP hx
  have hR := hc.copy.1
  have hlt := (th_x_lt_iff hR hi1 hik.le (by omega : 1 ≤ i + 1) hik).2 (by omega)
  have R := restr hc hi1 hik.le
  suffices h : (i : ℝ) + 1 ≤ (th Θ i).1 by linarith
  rcases mem_D428.1 (th_mem hc.copy hi1 hik.le) with h | h | h | h | h | h
  · obtain ⟨m, hm⟩ := (canon_bounds σ h).2.2.2.2.1
    rw [hm] at hx ⊢
    have : i < m := by exact_mod_cast hx
    have : i + 1 ≤ m := this
    exact_mod_cast this
  · have := (PL_props hc.lt h).1; have : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    linarith
  · have := R.2.1 h; omega
  · have hi := R.2.2.1 h; subst hi
    by_cases hbu : bp σ < up σ
    · exact ((PB_props h).2.2.2.2.1 hbu).le
    · have := (PB_props h).2.2.2.2.2.1 hbu; linarith
  · have hi := R.2.2.2 h; subst hi
    by_cases hbu : bp σ < up σ
    · have := (PU_props h).2.2.2.2.1 hbu; linarith
    · exact ((PU_props h).2.2.2.2.2.1 hbu).le
  · exact absurd h hnP

lemma c430_4 (hc : C σ a Θ) : ∀ i : ℕ, 1 < i → i ≤ k → th Θ i ∉ Pa428 σ a →
    (th Θ i).1 < (i : ℝ) → (th Θ (i - 1)).1 < (i : ℝ) - 1 := by
  intro i hi1 hik hnP hx
  have hR := hc.copy.1
  have hlt := (th_x_lt_iff hR (by omega : 1 ≤ i - 1) (by omega) (by omega) hik).2
    (by omega : i - 1 < i)
  have R := restr hc (by omega) hik
  suffices h : (th Θ i).1 ≤ (i : ℝ) - 1 by linarith
  rcases mem_D428.1 (th_mem hc.copy (by omega) hik) with h | h | h | h | h | h
  · obtain ⟨m, hm⟩ := (canon_bounds σ h).2.2.2.2.1
    rw [hm] at hx ⊢
    have : m < i := by exact_mod_cast hx
    have : m + 1 ≤ i := this
    have : (m : ℝ) + 1 ≤ i := by exact_mod_cast this
    linarith
  · have := R.1 h; omega
  · have := (PR_props hc.lt h).1; have : (i : ℝ) ≤ k := by exact_mod_cast hik
    linarith
  · have hi := R.2.2.1 h; subst hi
    by_cases hbu : bp σ < up σ
    · have := (PB_props h).2.2.2.2.1 hbu; linarith
    · exact ((PB_props h).2.2.2.2.2.1 hbu).le
  · have hi := R.2.2.2 h; subst hi
    by_cases hbu : bp σ < up σ
    · exact ((PU_props h).2.2.2.2.1 hbu).le
    · have := (PU_props h).2.2.2.2.2.1 hbu; linarith
  · exact absurd h hnP

lemma c431_1 (hc : C σ a Θ) : ∀ j : ℕ, 1 ≤ j → (j : ℝ) < (thInv σ Θ j).2 →
    (lv σ : ℝ) + 1 ≤ (thInv σ Θ j).2 → ∀ s : ℕ, j ≤ s → s ≤ k → (s : ℝ) < (thInv σ Θ s).2 := by
  intro j hj1 hy hyl
  have key := up_ind (fun s => (s : ℝ) < (thInv σ Θ s).2 ∧ (lv σ : ℝ) + 1 ≤ (thInv σ Θ s).2)
    (m := k) ⟨hy, hyl⟩ (by
      rintro s hjs hsk ⟨h1, h2⟩
      have hnP : thInv σ Θ s ∉ Pa428 σ a := fun h => by
        have := (Pa_props h).2.2.2.1; linarith
      have := c430_1 hc s (by omega) hsk hnP h1
      have hlt := (thInv_y_lt_iff hc.copy.1 (by omega) hsk.le (by omega) hsk).2
        (Nat.lt_succ_self s)
      exact ⟨by push_cast; linarith, by linarith⟩)
  intro s hjs hsk
  exact (key s hjs hsk).1

lemma c431_2 (hc : C σ a Θ) : ∀ j : ℕ, j ≤ k → (thInv σ Θ j).2 < (j : ℝ) →
    (thInv σ Θ j).2 ≤ (lv σ : ℝ) → ∀ s : ℕ, 1 ≤ s → s ≤ j → (thInv σ Θ s).2 < (s : ℝ) := by
  intro j hjk hy hyl
  have key := down_ind (fun s => (thInv σ Θ s).2 < (s : ℝ) ∧ (thInv σ Θ s).2 ≤ (lv σ : ℝ))
    ⟨hy, hyl⟩ (by
      rintro s hs1 hsj ⟨h1, h2⟩
      have hnP : thInv σ Θ s ∉ Pa428 σ a := fun h => by
        have := (Pa_props h).2.2.1; linarith
      have := c430_2 hc s hs1 (by omega) hnP h1
      have hlt := (thInv_y_lt_iff hc.copy.1 (by omega : 1 ≤ s - 1) (by omega) (by omega)
        (by omega : s ≤ k)).2 (by omega : s - 1 < s)
      refine ⟨?_, by linarith⟩
      rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]; exact this)
  intro s hs1 hsj
  exact (key s hs1 hsj).1

lemma c431_3 (hc : C σ a Θ) : ∀ i : ℕ, 1 ≤ i → (i : ℝ) < (th Θ i).1 →
    (a : ℝ) + 1 ≤ (th Θ i).1 → ∀ s : ℕ, i ≤ s → s ≤ k → (s : ℝ) < (th Θ s).1 := by
  intro i hi1 hx hxa
  have key := up_ind (fun s => (s : ℝ) < (th Θ s).1 ∧ (a : ℝ) + 1 ≤ (th Θ s).1)
    (m := k) ⟨hx, hxa⟩ (by
      rintro s his hsk ⟨h1, h2⟩
      have hnP : th Θ s ∉ Pa428 σ a := fun h => by
        have := (Pa_props h).2.1; linarith
      have := c430_3 hc s (by omega) hsk hnP h1
      have hlt := (th_x_lt_iff hc.copy.1 (by omega) hsk.le (by omega) hsk).2
        (Nat.lt_succ_self s)
      exact ⟨by push_cast; linarith, by linarith⟩)
  intro s his hsk
  exact (key s his hsk).1

lemma c431_4 (hc : C σ a Θ) : ∀ i : ℕ, i ≤ k → (th Θ i).1 < (i : ℝ) →
    (th Θ i).1 ≤ (a : ℝ) → ∀ s : ℕ, 1 ≤ s → s ≤ i → (th Θ s).1 < (s : ℝ) := by
  intro i hik hx hxa
  have key := down_ind (fun s => (th Θ s).1 < (s : ℝ) ∧ (th Θ s).1 ≤ (a : ℝ))
    ⟨hx, hxa⟩ (by
      rintro s hs1 hsi ⟨h1, h2⟩
      have hnP : th Θ s ∉ Pa428 σ a := fun h => by
        have := (Pa_props h).1; linarith
      have := c430_4 hc s hs1 (by omega) hnP h1
      have hlt := (th_x_lt_iff hc.copy.1 (by omega : 1 ≤ s - 1) (by omega) (by omega)
        (by omega : s ≤ k)).2 (by omega : s - 1 < s)
      refine ⟨?_, by linarith⟩
      rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]; exact this)
  intro s hs1 hsi
  exact (key s hs1 hsi).1


/-! ### Claim 4.32 -/

lemma Pa_lt_iff {p q : ℝ × ℝ} (hp : p ∈ Pa428 σ a) (hq : q ∈ Pa428 σ a) :
    p.1 < q.1 ↔ p.2 < q.2 := by
  have h1 := (Pa_props hp).2.2.2.2; have h2 := (Pa_props hq).2.2.2.2
  constructor <;> intro <;> linarith

lemma Pa_NI {p : ℝ × ℝ} (hp : p ∈ Pa428 σ a) : NI p := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hp
  intro m
  constructor
  · intro h
    simp only at h
    have e : t = ((m - a : ℤ) : ℝ) := by push_cast; linarith
    rw [e] at ht0 ht1
    have h0 : (0 : ℤ) < m - a := by exact_mod_cast ht0
    have h1 : m - a < (1 : ℤ) := by exact_mod_cast ht1
    omega
  · intro h
    simp only at h
    have e : t = ((m - lv σ : ℤ) : ℝ) := by push_cast; linarith
    rw [e] at ht0 ht1
    have h0 : (0 : ℤ) < m - lv σ := by exact_mod_cast ht0
    have h1 : m - lv σ < (1 : ℤ) := by exact_mod_cast ht1
    omega

lemma D428_canon_of_y (hlt : lv σ < rv σ) {p : ℝ × ℝ} (hp : p ∈ D428 σ a) {m : ℕ}
    (hm : p.2 = (m : ℝ)) : p ∈ canon σ := by
  have hNI : p ∉ canon σ → NI p := by
    intro hpc
    rcases mem_D428.1 hp with h | h | h | h | h | h
    · exact absurd h hpc
    · exact (PL_props hlt h).2.2.2.1
    · exact (PR_props hlt h).2.2.2.1
    · exact (PB_props h).2.2.2.1
    · exact (PU_props h).2.2.2.1
    · exact Pa_NI h
  by_contra hpc
  exact (hNI hpc m).2 (by rw [hm]; simp)

lemma rep_y_ne (hR : Represents σ Θ) {i j : Fin k} (h : i ≠ j) : (Θ i).2 ≠ (Θ j).2 := by
  intro he
  rcases lt_or_gt_of_ne (σ.injective.ne h) with h' | h'
  · have := (hR.2 i j).2 h'; rw [he] at this; exact lt_irrefl _ this
  · have := (hR.2 j i).2 h'; rw [he] at this; exact lt_irrefl _ this

/-- Replacing one point of a copy by a point in the same relative position gives a copy. -/
lemma rep_update (hR : Represents σ Θ) (i0 : Fin k) (q : ℝ × ℝ)
    (hx : ∀ i, i ≠ i0 → (Θ i).1 ≠ q.1 ∧ ((Θ i).1 < q.1 ↔ (Θ i).1 < (Θ i0).1))
    (hy : ∀ i, i ≠ i0 → (Θ i).2 ≠ q.2 ∧ ((Θ i).2 < q.2 ↔ (Θ i).2 < (Θ i0).2)) :
    Represents σ (Function.update Θ i0 q) := by
  constructor
  · intro i j hij
    by_cases hi : i = i0 <;> by_cases hj : j = i0
    · subst hi; subst hj; exact absurd hij (lt_irrefl _)
    · subst hi
      simp only [Function.update_self, Function.update_of_ne hj]
      have h1 := hR.1 hij
      have := hx j hj
      rcases lt_or_gt_of_ne this.1 with h | h
      · exact absurd (this.2.1 h) (not_lt.2 h1.le)
      · exact h
    · subst hj
      simp only [Function.update_self, Function.update_of_ne hi]
      exact (hx i hi).2.2 (hR.1 hij)
    · simp only [Function.update_of_ne hi, Function.update_of_ne hj]
      exact hR.1 hij
  · intro i j
    by_cases hi : i = i0 <;> by_cases hj : j = i0
    · subst hi; subst hj; simp
    · subst hi
      simp only [Function.update_self, Function.update_of_ne hj]
      rw [← hR.2]
      have h1 := hy j hj
      have h2 := rep_y_ne hR hj
      constructor
      · intro h
        rcases lt_or_gt_of_ne h2 with h3 | h3
        · exact absurd (h1.2.2 h3) (not_lt.2 h.le)
        · exact h3
      · intro h
        rcases lt_or_gt_of_ne h1.1 with h3 | h3
        · exact absurd (h1.2.1 h3) (not_lt.2 h.le)
        · exact h3
    · subst hj
      simp only [Function.update_self, Function.update_of_ne hi]
      rw [← hR.2]
      exact (hy i hi).2
    · simp only [Function.update_of_ne hi, Function.update_of_ne hj]
      exact hR.2 i j

/-- Claim 4.32, the case of two points: `Θ(1)` and `Θ(k)` are not both on `P_a`. -/
lemma not_both (hc : C σ a Θ) (h1 : th Θ 1 ∈ Pa428 σ a) (hk : th Θ k ∈ Pa428 σ a) : False := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl, hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  obtain ⟨hrl, -, -, ha2, hak, -⟩ := hc.casts
  have hR := hc.copy.1
  have key : ∀ i, 2 ≤ i → i ≤ 3 →
      (th Θ i ∈ PB419 σ ∧ i = bp σ) ∨ (th Θ i ∈ PU419 σ ∧ i = up σ) := by
    intro i hi2 hi3
    have hx1 := (th_x_lt_iff hR le_rfl (by omega) (by omega) (by omega)).2 (by omega : 1 < i)
    have hxk := (th_x_lt_iff hR (by omega) (by omega) (by omega) le_rfl).2 (by omega : i < k)
    have hP1 := Pa_props h1
    have hPk := Pa_props hk
    have R := restr hc (by omega : 1 ≤ i) (by omega : i ≤ k)
    rcases mem_D428.1 (th_mem hc.copy (by omega : 1 ≤ i) (by omega : i ≤ k)) with
      h | h | h | h | h | h
    · exfalso
      obtain ⟨m, hm⟩ := (canon_bounds σ h).2.2.2.2.1
      have e1 : (a : ℝ) < m := by linarith
      have e2 : (m : ℝ) < a + 1 := by linarith
      have e1' : a < m := by exact_mod_cast e1
      have e2' : m < a + 1 := by exact_mod_cast e2
      omega
    · exfalso; have := (PL_props hc.lt h).1; linarith
    · exfalso; have := (PR_props hc.lt h).1; linarith
    · exact Or.inl ⟨h, R.2.2.1 h⟩
    · exact Or.inr ⟨h, R.2.2.2 h⟩
    · exfalso
      have y1 := (Pa_lt_iff h1 h).1 hx1
      have yk := (Pa_lt_iff h hk).1 hxk
      rw [th_y_lt_iff hR le_rfl (by omega) (by omega) (by omega)] at y1
      rw [th_y_lt_iff hR (by omega) (by omega) (by omega) le_rfl] at yk
      have hlr := hc.lr
      unfold lv rv at *
      omega
  have hx23 := (th_x_lt_iff hR (by omega : 1 ≤ 2) (by omega) (by omega) (by omega)).2
    (by omega : 2 < 3)
  rcases key 2 le_rfl (by omega) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
    rcases key 3 (by omega) le_rfl with ⟨h3, e3⟩ | ⟨h3, e3⟩
  · omega
  · have hbu' : bp σ < up σ := by omega
    have := (PB_props h2).2.2.2.2.1 hbu'
    have := (PU_props h3).2.2.2.2.1 hbu'
    rw [← e2] at *; rw [← e3] at *; push_cast at *; linarith
  · have hbu' : ¬ bp σ < up σ := by omega
    have := (PU_props h2).2.2.2.2.2.1 hbu'
    have := (PB_props h3).2.2.2.2.2.1 hbu'
    rw [← e2] at *; rw [← e3] at *; push_cast at *; linarith
  · omega

/-- If `Θ(1)` and another point of `Θ` lie on `P_a`, then so does `Θ(k)`. A step inside the proof by
contradiction of Claim 4.32 (tex l.1301): its hypotheses can never all hold, as `UG.c432` shows;
used only inside the case split of `UG.c432`. -/
lemma first_other (hc : C σ a Θ) (h1 : th Θ 1 ∈ Pa428 σ a) {i : ℕ} (hi1 : 1 < i) (hik : i ≤ k)
    (hi : th Θ i ∈ Pa428 σ a) : th Θ k ∈ Pa428 σ a := by
  obtain ⟨hk4, hl2, hrk, -⟩ := facts hc.standing hc.lr
  have hR := hc.copy.1
  have y1 := (Pa_lt_iff h1 hi).1 ((th_x_lt_iff hR le_rfl (by omega) (by omega) hik).2 hi1)
  have y1' := y1
  rw [th_y_lt_iff hR le_rfl (by omega) (by omega) hik] at y1'
  rcases eq_or_lt_of_le (show i ≤ k from hik) with he | hlt
  · rw [he] at hi; exact hi
  · have hsi : sval σ i ≠ sval σ k := fun h => by
      have := sval_inj σ (by omega) hik (by omega) le_rfl h; omega
    have hlr := hc.lr
    unfold lv rv at hlr
    have hvk : sval σ k < sval σ i := by omega
    have yk := (th_y_lt_iff hR (by omega) le_rfl (by omega) hik).2 hvk
    have yk1 := (th_y_lt_iff hR le_rfl (by omega) (by omega) le_rfl).2 (by unfold lv at *; omega)
    exact band_Pa hc.lr (th_mem hc.copy (by omega) le_rfl)
      (by have := (Pa_props h1).2.2.1; linarith) (by have := (Pa_props hi).2.2.2.1; linarith)

/-- If `Θ(k)` and another point of `Θ` lie on `P_a`, then so does `Θ(1)`. A step inside the proof by
contradiction of Claim 4.32 (tex l.1301): its hypotheses can never all hold, as `UG.c432` shows;
used only inside the case split of `UG.c432`. -/
lemma last_other (hc : C σ a Θ) (hk : th Θ k ∈ Pa428 σ a) {i : ℕ} (hi1 : 1 ≤ i) (hik : i < k)
    (hi : th Θ i ∈ Pa428 σ a) : th Θ 1 ∈ Pa428 σ a := by
  obtain ⟨hk4, hl2, hrk, -⟩ := facts hc.standing hc.lr
  have hR := hc.copy.1
  have yk := (Pa_lt_iff hi hk).1 ((th_x_lt_iff hR hi1 hik.le (by omega) le_rfl).2 hik)
  have yk' := yk
  rw [th_y_lt_iff hR hi1 hik.le (by omega) le_rfl] at yk'
  rcases eq_or_lt_of_le (show 1 ≤ i from hi1) with he | hlt
  · rw [← he] at hi; exact hi
  · have hsi : sval σ i ≠ sval σ 1 := fun h => by
      have := sval_inj σ hi1 hik.le le_rfl (by omega) h; omega
    have hlr := hc.lr
    unfold lv rv at hlr
    have hv1 : sval σ i < sval σ 1 := by omega
    have y1 := (th_y_lt_iff hR hi1 hik.le le_rfl (by omega)).2 hv1
    have y1k := (th_y_lt_iff hR le_rfl (by omega) (by omega) le_rfl).2 (by omega)
    exact band_Pa hc.lr (th_mem hc.copy le_rfl (by omega))
      (by have := (Pa_props hi).2.2.1; linarith) (by have := (Pa_props hk).2.2.2.1; linarith)


/-- Claim 4.32, the case where `Θ(1)` is the only point of `Θ` on `P_a`: this case is
impossible, since replacing `Θ(1)` by `Σ(1)` would give a `σ`-copy in the support of
Construction 4.19 other than `Σ`, contradicting Lemma 4.20. -/
lemma only_first (hc : C σ a Θ) (h1 : th Θ 1 ∈ Pa428 σ a)
    (hno : ∀ i, 1 < i → i ≤ k → th Θ i ∉ Pa428 σ a) : False := by
  classical
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl, hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  obtain ⟨hrl, -, -, ha2, hak, -⟩ := hc.casts
  have hR := hc.copy.1
  set i0 : Fin k := ⟨0, by omega⟩ with hi0
  have e0 : th Θ 1 = Θ i0 := th_fin Θ i0
  have hno' : ∀ i : Fin k, i ≠ i0 → Θ i ∉ Pa428 σ a ∧ (Θ i0).1 < (Θ i).1 := by
    intro i hi
    have hv : i.val ≠ 0 := fun h => hi (Fin.ext h)
    refine ⟨?_, hR.1 (Fin.lt_def.2 (by simp [i0]; omega))⟩
    rw [← th_fin Θ i]; exact hno _ (by omega) (by omega)
  set q : ℝ × ℝ := (1, (lv σ : ℝ)) with hq
  have hqc : q ∈ canon σ := (mem_canon σ).2 ⟨1, le_rfl, by omega, by simp [q, lv]⟩
  have hP0 := Pa_props (e0 ▸ h1)
  have hR' := rep_update hR i0 q
    (fun i hi => by
      obtain ⟨-, hlt⟩ := hno' i hi
      have : (1 : ℝ) < (Θ i).1 := by linarith [hP0.1]
      refine ⟨by simp only [q]; linarith, fun h => by simp only [q] at h; linarith,
        fun h => by linarith⟩)
    (fun i hi => by
      obtain ⟨hnP, hlt⟩ := hno' i hi
      have hD := hc.copy.2 i
      have hband : ¬ ((lv σ : ℝ) < (Θ i).2 ∧ (Θ i).2 < lv σ + 1) := fun h =>
        hnP (band_Pa hc.lr hD h.1 h.2)
      have hne : (Θ i).2 ≠ lv σ := by
        intro he
        have hcan := D428_canon_of_y hc.lt hD he
        obtain ⟨-, -, hp⟩ := canon_of_y σ hcan he
        rw [hsl] at hp
        have := congrArg Prod.fst hp
        simp only [Nat.cast_one] at this
        linarith [hP0.1]
      refine ⟨hne, fun h => by simp only [q] at h; linarith [hP0.2.2.1], fun h => ?_⟩
      simp only [q]
      by_contra hcon
      push Not at hcon
      exact hband ⟨lt_of_le_of_ne hcon (Ne.symm hne), by linarith [hP0.2.2.2.1]⟩)
  have hcopy : CopyIn σ (Function.update Θ i0 q) (D419 σ) := by
    refine ⟨hR', fun i => ?_⟩
    by_cases hi : i = i0
    · subst hi; rw [Function.update_self]; exact canon_subset_D419 hqc
    · rw [Function.update_of_ne hi]
      exact Or.resolve_right (hc.copy.2 i) (hno' i hi).1
  have himg := copy_D419_eq hc.standing hc.lt hcopy
  have hw : (((2 : ℕ) : ℝ), (sval σ 2 : ℝ)) ∈ canon σ :=
    (mem_canon σ).2 ⟨2, by omega, by omega, rfl⟩
  rw [← himg] at hw
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hw
  by_cases hii : i = i0
  · subst hii
    rw [Function.update_self] at hi
    have := congrArg Prod.fst hi
    simp only [q] at this; norm_num at this
  · rw [Function.update_of_ne hii] at hi
    have := (hno' i hii).2
    have h2 := congrArg Prod.fst hi
    simp only at h2
    push_cast at h2
    linarith [hP0.1]

/-- Claim 4.32, the case where `Θ(k)` is the only point of `Θ` on `P_a`. -/
lemma only_last (hc : C σ a Θ) (hk : th Θ k ∈ Pa428 σ a)
    (hno : ∀ i, 1 ≤ i → i < k → th Θ i ∉ Pa428 σ a) : False := by
  classical
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl, hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  obtain ⟨hrl, -, -, ha2, hak, -⟩ := hc.casts
  have hR := hc.copy.1
  set i0 : Fin k := ⟨k - 1, by omega⟩ with hi0
  have e0 : th Θ k = Θ i0 := by
    rw [← th_fin Θ i0]; congr 1; simp [i0]; omega
  have hno' : ∀ i : Fin k, i ≠ i0 → Θ i ∉ Pa428 σ a ∧ (Θ i).1 < (Θ i0).1 := by
    intro i hi
    have hv : i.val ≠ k - 1 := fun h => hi (Fin.ext h)
    have := i.isLt
    refine ⟨?_, hR.1 (Fin.lt_def.2 (by simp [i0]; omega))⟩
    rw [← th_fin Θ i]; exact hno _ (by omega) (by omega)
  set q : ℝ × ℝ := ((k : ℝ), (rv σ : ℝ)) with hq
  have hqc : q ∈ canon σ := (mem_canon σ).2 ⟨k, by omega, le_rfl, by simp [q, rv]⟩
  have hP0 := Pa_props (e0 ▸ hk)
  have hR' := rep_update hR i0 q
    (fun i hi => by
      obtain ⟨-, hlt⟩ := hno' i hi
      have : (Θ i).1 < (k : ℝ) - 1 := by linarith [hP0.2.1]
      refine ⟨by simp only [q]; linarith, fun _ => by linarith [hP0.2.1],
        fun _ => by simp only [q]; linarith⟩)
    (fun i hi => by
      obtain ⟨hnP, hlt⟩ := hno' i hi
      have hD := hc.copy.2 i
      have hband : ¬ ((lv σ : ℝ) < (Θ i).2 ∧ (Θ i).2 < lv σ + 1) := fun h =>
        hnP (band_Pa hc.lr hD h.1 h.2)
      have hne : (Θ i).2 ≠ rv σ := by
        intro he
        have hcan := D428_canon_of_y hc.lt hD he
        obtain ⟨-, -, hp⟩ := canon_of_y σ hcan he
        rw [hsr] at hp
        have := congrArg Prod.fst hp
        simp only at this
        linarith [hP0.2.1]
      refine ⟨hne, fun h => ?_, fun h => by simp only [q]; linarith [hP0.2.2.2.1]⟩
      simp only [q] at h
      by_contra hcon
      push Not at hcon
      have : (Θ i).2 ≤ lv σ := by
        by_contra h'
        push Not at h'
        exact hband ⟨h', by linarith⟩
      linarith [hP0.2.2.1])
  have hcopy : CopyIn σ (Function.update Θ i0 q) (D419 σ) := by
    refine ⟨hR', fun i => ?_⟩
    by_cases hi : i = i0
    · subst hi; rw [Function.update_self]; exact canon_subset_D419 hqc
    · rw [Function.update_of_ne hi]
      exact Or.resolve_right (hc.copy.2 i) (hno' i hi).1
  have himg := copy_D419_eq hc.standing hc.lt hcopy
  have hw : (((k - 1 : ℕ) : ℝ), (sval σ (k - 1) : ℝ)) ∈ canon σ :=
    (mem_canon σ).2 ⟨k - 1, by omega, by omega, rfl⟩
  rw [← himg] at hw
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hw
  have hc1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  by_cases hii : i = i0
  · subst hii
    rw [Function.update_self] at hi
    have := congrArg Prod.fst hi
    simp only [q] at this
    rw [hc1] at this; linarith
  · rw [Function.update_of_ne hii] at hi
    have := (hno' i hii).2
    have h2 := congrArg Prod.fst hi
    simp only at h2
    rw [hc1] at h2
    linarith [hP0.2.1]

/-- **Claim 4.32** in the auxiliary context. -/
lemma c432 (hc : C σ a Θ) : th Θ 1 ∉ Pa428 σ a ∧ th Θ k ∉ Pa428 σ a := by
  constructor
  · intro h1
    by_cases hex : ∃ i, 1 < i ∧ i ≤ k ∧ th Θ i ∈ Pa428 σ a
    · obtain ⟨i, hi1, hik, hi⟩ := hex
      exact not_both hc h1 (first_other hc h1 hi1 hik hi)
    · push Not at hex; exact only_first hc h1 hex
  · intro hk
    by_cases hex : ∃ i, 1 ≤ i ∧ i < k ∧ th Θ i ∈ Pa428 σ a
    · obtain ⟨i, hi1, hik, hi⟩ := hex
      exact not_both hc (last_other hc hk hi1 hik hi) hk
    · push Not at hex; exact only_last hc hk hex


/-! ### Claims 4.33 and 4.34 -/

/-- **Claim 4.33 (1)** in the auxiliary context. -/
lemma c433_1 (hc : C σ a Θ) (hs : ∃ s : ℕ, 1 ≤ s ∧ s < lv σ ∧ thInv σ Θ s ∈ Pa428 σ a) :
    (lv σ : ℝ) + 1 ≤ (thInv σ Θ (lv σ)).2 ∧ thInv σ Θ k ∈ PU419 σ ∧
      ∀ j : ℕ, rv σ ≤ j → j ≤ k - 1 → thInv σ Θ j = sigInv σ (j + 1) := by
  obtain ⟨s, hs1, hsl, hsP⟩ := hs
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl', hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  obtain ⟨hrl, -⟩ := hc.casts
  have hlr := hc.lr
  have hR := hc.copy.1
  have hy1 := (thInv_y_lt_iff hR hs1 (by omega) (by omega) (by omega)).2 hsl
  have hPs := Pa_props hsP
  have hL1 : thInv σ Θ (lv σ) = th Θ 1 := by rw [thInv_eq_th σ Θ (by omega) (by omega), hsl']
  have hnP : thInv σ Θ (lv σ) ∉ Pa428 σ a := by rw [hL1]; exact (c432 hc).1
  have hyl : (lv σ : ℝ) + 1 ≤ (thInv σ Θ (lv σ)).2 := by
    by_contra h; push Not at h
    exact hnP (band_Pa hc.lr (thInv_mem hc.copy (by omega) (by omega))
      (by linarith) h)
  have hprop := c431_1 hc (lv σ) (by omega) (by linarith) hyl
  have hU : thInv σ Θ k ∈ PU419 σ :=
    band_U hc.lr (thInv_mem hc.copy (by omega) le_rfl) (hprop k (by omega) le_rfl)
  refine ⟨hyl, hU, ?_⟩
  have hcan : ∀ j, rv σ ≤ j → j ≤ k - 1 →
      ∃ m : ℕ, (thInv σ Θ j).2 = m ∧ thInv σ Θ j ∈ canon σ ∧ j + 1 ≤ m := by
    intro j hj1 hj2
    have hyj := hprop j (by omega) (by omega)
    have R := restrInv hc (j := j) (by omega) (by omega)
    rcases mem_D428.1 (thInv_mem hc.copy (j := j) (by omega) (by omega)) with
      h | h | h | h | h | h
    · obtain ⟨m, hm⟩ := (canon_bounds σ h).2.2.2.2.2
      refine ⟨m, hm, h, ?_⟩
      rw [hm] at hyj
      have : j < m := by exact_mod_cast hyj
      omega
    · have := R.1 h; omega
    · exfalso; have := R.2.1 h; subst this; have := (PR_props hc.lt h).2.1; linarith
    · have := R.2.2.1 h; omega
    · have := R.2.2.2 h; omega
    · exfalso; have := (Pa_props h).2.2.2.1
      have : (rv σ : ℝ) ≤ j := by exact_mod_cast hj1
      linarith
  have hle : ∀ j, 1 ≤ j → j ≤ k - 1 → (rv σ ≤ j → (thInv σ Θ j).2 ≤ (j : ℝ) + 1) := by
    refine down_ind (fun j => rv σ ≤ j → (thInv σ Θ j).2 ≤ (j : ℝ) + 1) ?_ ?_
    · intro hj
      obtain ⟨m, hm, hmc, -⟩ := hcan (k - 1) hj le_rfl
      have := (canon_bounds σ hmc).2.2.2.1
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]; linarith
    · intro s hs1 hsk ih hrs
      obtain ⟨m, hm, -, -⟩ := hcan (s - 1) hrs (by omega)
      have hlt := (thInv_y_lt_iff hR (by omega : 1 ≤ s - 1) (by omega) (by omega)
        (by omega : s ≤ k)).2 (by omega : s - 1 < s)
      have := ih (by omega)
      rw [hm] at hlt ⊢
      have h' : (m : ℝ) < s + 1 := by linarith
      have h'' : m < s + 1 := by exact_mod_cast h'
      have : m ≤ s - 1 + 1 := by omega
      exact_mod_cast this
  intro j hj1 hj2
  obtain ⟨m, hm, hmc, hjm⟩ := hcan j hj1 hj2
  have := hle j (by omega) hj2 hj1
  rw [hm] at this
  have hm' : m ≤ j + 1 := by exact_mod_cast this
  have hmj : m = j + 1 := by omega
  obtain ⟨-, -, hp⟩ := canon_of_y σ hmc hm
  rw [hp, sigInv_eq σ (by omega) (by omega), hmj]

/-- **Claim 4.33 (2)** in the auxiliary context. -/
lemma c433_2 (hc : C σ a Θ) (hs : ∃ s : ℕ, rv σ < s ∧ s ≤ k ∧ thInv σ Θ s ∈ Pa428 σ a) :
    (thInv σ Θ (rv σ)).2 ≤ (lv σ : ℝ) ∧ thInv σ Θ 1 ∈ PB419 σ ∧
      ∀ j : ℕ, 2 ≤ j → j ≤ lv σ → thInv σ Θ j = sigInv σ (j - 1) := by
  obtain ⟨s, hs1, hsk, hsP⟩ := hs
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl', hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  obtain ⟨hrl, -⟩ := hc.casts
  have hlr := hc.lr
  have hR := hc.copy.1
  have hy1 := (thInv_y_lt_iff hR (j := rv σ) (by omega) (by omega) (by omega) hsk).2 hs1
  have hPs := Pa_props hsP
  have hRk : thInv σ Θ (rv σ) = th Θ k := by rw [thInv_eq_th σ Θ (by omega) (by omega), hsr]
  have hnP : thInv σ Θ (rv σ) ∉ Pa428 σ a := by rw [hRk]; exact (c432 hc).2
  have hyl : (thInv σ Θ (rv σ)).2 ≤ lv σ := by
    by_contra h; push Not at h
    exact hnP (band_Pa hc.lr (thInv_mem hc.copy (by omega) (by omega))
      h (by linarith))
  have hprop := c431_2 hc (rv σ) (by omega) (by rw [hrl]; linarith) hyl
  have hB : thInv σ Θ 1 ∈ PB419 σ := band_B hc.lr (thInv_mem hc.copy le_rfl (by omega))
    (by have := hprop 1 le_rfl (by omega); simpa using this)
  refine ⟨hyl, hB, ?_⟩
  have hcan : ∀ j, 2 ≤ j → j ≤ lv σ →
      ∃ m : ℕ, (thInv σ Θ j).2 = m ∧ thInv σ Θ j ∈ canon σ ∧ m + 1 ≤ j := by
    intro j hj1 hj2
    have hyj := hprop j (by omega) (by omega)
    have R := restrInv hc (j := j) (by omega) (by omega)
    rcases mem_D428.1 (thInv_mem hc.copy (j := j) (by omega) (by omega)) with
      h | h | h | h | h | h
    · obtain ⟨m, hm⟩ := (canon_bounds σ h).2.2.2.2.2
      refine ⟨m, hm, h, ?_⟩
      rw [hm] at hyj
      have : m < j := by exact_mod_cast hyj
      omega
    · exfalso; have := R.1 h; subst this; have := (PL_props hc.lt h).2.1; linarith
    · have := R.2.1 h; omega
    · have := R.2.2.1 h; omega
    · exfalso; have := (PU_props h).1
      have : (j : ℝ) ≤ k := by exact_mod_cast (show j ≤ k by omega)
      linarith
    · exfalso; have := (Pa_props h).2.2.1
      have : (j : ℝ) ≤ lv σ := by exact_mod_cast hj2
      linarith
  have hge : ∀ j, 2 ≤ j → j ≤ lv σ → (j : ℝ) - 1 ≤ (thInv σ Θ j).2 := by
    refine up_ind (fun j => (j : ℝ) - 1 ≤ (thInv σ Θ j).2) ?_ ?_
    · obtain ⟨m, hm, hmc, -⟩ := hcan 2 le_rfl (by omega)
      have := (canon_bounds σ hmc).2.2.1
      norm_num; linarith
    · intro s hs2 hsl ih
      obtain ⟨m, hm, -, -⟩ := hcan (s + 1) (by omega) (by omega)
      have hlt := (thInv_y_lt_iff hR (by omega : 1 ≤ s) (by omega) (by omega)
        (by omega : s + 1 ≤ k)).2 (by omega : s < s + 1)
      rw [hm] at hlt ⊢
      have h'' : s < m + 1 := by
        have : (s : ℝ) < m + 1 := by linarith
        exact_mod_cast this
      have : s ≤ m := by omega
      have : (s : ℝ) ≤ m := by exact_mod_cast this
      push_cast
      linarith
  intro j hj1 hj2
  obtain ⟨m, hm, hmc, hjm⟩ := hcan j hj1 hj2
  have := hge j hj1 hj2
  rw [hm] at this
  have hm' : j ≤ m + 1 := by
    have : (j : ℝ) ≤ m + 1 := by linarith
    exact_mod_cast this
  have hmj : j - 1 = m := by omega
  obtain ⟨-, -, hp⟩ := canon_of_y σ hmc hm
  rw [hp, sigInv_eq σ (by omega) (by omega), hmj]

/-- **Claim 4.34 (1)** in the auxiliary context (the condition (UD) written out). -/
lemma c434_1 (hc : C σ a Θ) (hs : ∃ s : ℕ, 1 ≤ s ∧ s < lv σ ∧ thInv σ Θ s ∈ Pa428 σ a) :
    (∀ j : ℕ, rv σ ≤ j → j < k → spos σ (j + 1) < spos σ j) ∧
      (thInv σ Θ k).1 < (up σ : ℝ) - 1 ∧ bp σ < up σ := by
  obtain ⟨-, hU, hsh⟩ := c433_1 hc hs
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl', hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  have hlr := hc.lr
  have hR := hc.copy.1
  have hUD : ∀ j : ℕ, rv σ ≤ j → j < k → spos σ (j + 1) < spos σ j := by
    intro j hj1 hj2
    refine up_ind (fun j => j < k → spos σ (j + 1) < spos σ j) (m := k) ?_ ?_ j hj1 (by omega) hj2
    · intro _
      have h1 := spos_range σ (j := rv σ + 1) (by omega) (by omega)
      have h2 : spos σ (rv σ + 1) ≠ spos σ (rv σ) := fun h => by
        have := spos_inj σ (by omega) (by omega) (by omega) (by omega) h; omega
      omega
    · intro s hrs hsk ih hs1
      have e1 := hsh s hrs (by omega)
      have e2 := hsh (s + 1) (by omega) (by omega)
      have hx := thInv_x_lt_iff hR (j := s) (j' := s + 1) (by omega) (by omega) (by omega)
        (by omega)
      rw [e1, e2, sigInv_eq σ (by omega) (by omega), sigInv_eq σ (by omega) (by omega)] at hx
      simp only [Nat.cast_lt] at hx
      have := ih (by omega)
      have hne : spos σ (s + 1 + 1) ≠ spos σ (s + 1) := fun h => by
        have := spos_inj σ (by omega) (by omega) (by omega) (by omega) h; omega
      by_contra hcon
      have := hx.1 (lt_of_le_of_ne (not_lt.1 hcon) hne.symm)
      omega
  refine ⟨hUD, ?_⟩
  have h1 := hUD (k - 1) (by omega) (by omega)
  rw [show k - 1 + 1 = k by omega] at h1
  have hx := (thInv_x_lt_iff hR (j := k) (j' := k - 1) (by omega) le_rfl (by omega)
    (by omega)).2 h1
  rw [hsh (k - 1) (by omega) le_rfl, show k - 1 + 1 = k by omega,
    sigInv_eq σ (by omega) le_rfl] at hx
  simp only at hx
  have hbu' : bp σ < up σ := by
    by_contra h
    have := (PU_props hU).2.2.2.2.2.1 h
    unfold up at this; linarith
  exact ⟨(PU_props hU).2.2.2.2.1 hbu', hbu'⟩

/-- **Claim 4.34 (2)** in the auxiliary context (the condition (BD) written out). -/
lemma c434_2 (hc : C σ a Θ) (hs : ∃ s : ℕ, rv σ < s ∧ s ≤ k ∧ thInv σ Θ s ∈ Pa428 σ a) :
    (∀ j : ℕ, 1 ≤ j → j < lv σ → spos σ (j + 1) < spos σ j) ∧
      (bp σ : ℝ) + 1 < (thInv σ Θ 1).1 ∧ bp σ < up σ := by
  obtain ⟨-, hB, hsh⟩ := c433_2 hc hs
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl', hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  have hlr := hc.lr
  have hR := hc.copy.1
  have hBD : ∀ j : ℕ, 1 ≤ j → j < lv σ → spos σ (j + 1) < spos σ j := by
    intro j hj1 hj2
    refine down_ind (fun j => j < lv σ → spos σ (j + 1) < spos σ j) (j := lv σ - 1) ?_ ?_ j hj1
      (by omega) hj2
    · intro _
      rw [show lv σ - 1 + 1 = lv σ by omega, hsl']
      have h1 := spos_range σ (j := lv σ - 1) (by omega) (by omega)
      have h2 : spos σ (lv σ - 1) ≠ spos σ (lv σ) := fun h => by
        have := spos_inj σ (by omega) (by omega) (by omega) (by omega) h; omega
      omega
    · intro s hs1 hsl ih hlt
      rw [show s - 1 + 1 = s by omega]
      have e1 := hsh s (by omega) (by omega)
      have e2 := hsh (s + 1) (by omega) (by omega)
      rw [show s + 1 - 1 = s by omega] at e2
      have hx := thInv_x_lt_iff hR (j := s) (j' := s + 1) (by omega) (by omega) (by omega)
        (by omega)
      rw [e1, e2, sigInv_eq σ (by omega) (by omega), sigInv_eq σ (by omega) (by omega)] at hx
      simp only [Nat.cast_lt] at hx
      have := ih (by omega)
      have hne : spos σ (s - 1) ≠ spos σ s := fun h => by
        have := spos_inj σ (by omega) (by omega) (by omega) (by omega) h; omega
      by_contra hcon
      have := hx.1 (lt_of_le_of_ne (not_lt.1 hcon) hne)
      omega
  refine ⟨hBD, ?_⟩
  have h1 := hBD 1 le_rfl (by omega)
  have hx := (thInv_x_lt_iff hR (j := 2) (j' := 1) (by omega) (by omega) le_rfl
    (by omega)).2 h1
  rw [hsh 2 le_rfl (by omega), sigInv_eq σ le_rfl (by omega)] at hx
  simp only at hx
  have hbu' : bp σ < up σ := by
    by_contra h
    have := (PB_props hB).2.2.2.2.2.1 h
    unfold bp at this; linarith
  exact ⟨(PB_props hB).2.2.2.2.1 hbu', hbu'⟩


/-! ### Claim 4.36 and its mirror -/

/-- **Claim 4.36** in the auxiliary context; neither (UD) nor the failure of (BD) is needed. -/
lemma c436 (hc : C σ a Θ) {s : ℕ} (hs : 1 ≤ s ∧ s < lv σ) (hsP : thInv σ Θ s ∈ Pa428 σ a) :
    ∀ t : ℕ, s ≤ t → t < lv σ → thInv σ Θ t ∈ Pa428 σ a := by
  intro t hst htl
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl', hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  obtain ⟨hrl, hl2', hlk', -⟩ := hc.casts
  have hlr := hc.lr
  obtain ⟨-, -, hsh⟩ := c433_1 hc ⟨s, hs.1, hs.2, hsP⟩
  have hR := hc.copy.1
  have hPs := Pa_props hsP
  have hyt1 : (lv σ : ℝ) < (thInv σ Θ t).2 := by
    rcases eq_or_lt_of_le hst with h | h
    · subst h; exact hPs.2.2.1
    · have := (thInv_y_lt_iff hR (j := s) (j' := t) hs.1 (by omega) (by omega) (by omega)).2 h
      linarith [hPs.2.2.1]
  have hr := hsh (rv σ) le_rfl (by omega)
  rw [sigInv_eq σ (by omega) (by omega)] at hr
  have hyt2 : (thInv σ Θ t).2 < (rv σ : ℝ) + 1 := by
    have := (thInv_y_lt_iff hR (j := t) (j' := rv σ) (by omega) (by omega) (by omega)
      (by omega)).2 (by omega)
    rw [hr] at this; push_cast at this; exact this
  have hxt : (thInv σ Θ t).1 < (thInv σ Θ (rv σ)).1 := by
    rw [thInv_x_lt_iff hR (by omega) (by omega) (by omega) (by omega), hsr]
    have h1 := spos_range σ (j := t) (by omega) (by omega)
    have h2 : spos σ t ≠ spos σ (rv σ) := fun h => by
      have := spos_inj σ (by omega) (by omega) (by omega) (by omega) h; omega
    rw [hsr] at h2; omega
  rw [hr] at hxt
  simp only at hxt
  have hsk := spos_range σ (j := rv σ + 1) (by omega) (by omega)
  have hsk' : (spos σ (rv σ + 1) : ℝ) ≤ k := by exact_mod_cast hsk.2
  have R := restrInv hc (j := t) (by omega) (by omega)
  rcases mem_D428.1 (thInv_mem hc.copy (j := t) (by omega) (by omega)) with h | h | h | h | h | h
  · exfalso
    obtain ⟨m, hm⟩ := (canon_bounds σ h).2.2.2.2.2
    rw [hm] at hyt1 hyt2
    have e1 : lv σ < m := by exact_mod_cast hyt1
    have e2 : m < rv σ + 1 := by exact_mod_cast hyt2
    have hmr : m = rv σ := by omega
    obtain ⟨-, -, hp⟩ := canon_of_y σ h hm
    rw [hmr, hsr] at hp
    have := congrArg Prod.fst hp
    simp only at this
    linarith
  · have := R.1 h; omega
  · exfalso; have := (PR_props hc.lt h).2.1; linarith
  · exfalso; have := (PB_props h).1; linarith
  · exfalso; have := (PU_props h).1; linarith
  · exact h

/-- The mirror of Claim 4.36 (for ranks above `r`). -/
lemma c436m (hc : C σ a Θ) {s : ℕ} (hs : rv σ < s ∧ s ≤ k) (hsP : thInv σ Θ s ∈ Pa428 σ a) :
    ∀ t : ℕ, rv σ < t → t ≤ s → thInv σ Θ t ∈ Pa428 σ a := by
  intro t hrt hts
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl', hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  obtain ⟨hrl, hl2', hlk', -⟩ := hc.casts
  have hlr := hc.lr
  obtain ⟨-, -, hsh⟩ := c433_2 hc ⟨s, hs.1, hs.2, hsP⟩
  have hR := hc.copy.1
  have hPs := Pa_props hsP
  have hyt2 : (thInv σ Θ t).2 < (lv σ : ℝ) + 1 := by
    rcases eq_or_lt_of_le hts with h | h
    · subst h; exact hPs.2.2.2.1
    · have := (thInv_y_lt_iff hR (j := t) (j' := s) (by omega) (by omega) (by omega) hs.2).2 h
      linarith [hPs.2.2.2.1]
  have hl := hsh (lv σ) (by omega) le_rfl
  rw [sigInv_eq σ (by omega) (by omega)] at hl
  have hc1 : ((lv σ - 1 : ℕ) : ℝ) = (lv σ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ lv σ), Nat.cast_one]
  have hyt1 : (lv σ : ℝ) - 1 < (thInv σ Θ t).2 := by
    have := (thInv_y_lt_iff hR (j := lv σ) (j' := t) (by omega) (by omega) (by omega)
      (by omega)).2 (by omega)
    rw [hl] at this; simp only at this; rw [hc1] at this; exact this
  have hxt : (thInv σ Θ (lv σ)).1 < (thInv σ Θ t).1 := by
    rw [thInv_x_lt_iff hR (by omega) (by omega) (by omega) (by omega), hsl']
    have h1 := spos_range σ (j := t) (by omega) (by omega)
    have h2 : spos σ t ≠ spos σ (lv σ) := fun h => by
      have := spos_inj σ (by omega) (by omega) (by omega) (by omega) h; omega
    rw [hsl'] at h2; omega
  rw [hl] at hxt
  simp only at hxt
  have hs1 := spos_range σ (j := lv σ - 1) (by omega) (by omega)
  have hs1' : (1 : ℝ) ≤ spos σ (lv σ - 1) := by exact_mod_cast hs1.1
  have R := restrInv hc (j := t) (by omega) (by omega)
  rcases mem_D428.1 (thInv_mem hc.copy (j := t) (by omega) (by omega)) with h | h | h | h | h | h
  · exfalso
    obtain ⟨m, hm⟩ := (canon_bounds σ h).2.2.2.2.2
    rw [hm] at hyt1 hyt2
    have e1 : lv σ < m + 1 := by
      have : (lv σ : ℝ) < m + 1 := by linarith
      exact_mod_cast this
    have e2 : m < lv σ + 1 := by exact_mod_cast hyt2
    have hmr : m = lv σ := by omega
    obtain ⟨-, -, hp⟩ := canon_of_y σ h hm
    rw [hmr, hsl'] at hp
    have := congrArg Prod.fst hp
    simp only [Nat.cast_one] at this
    linarith
  · exfalso; have := (PL_props hc.lt h).2.1; linarith
  · have := R.2.1 h; omega
  · exfalso; have := (PB_props h).1; linarith
  · exfalso; have := (PU_props h).1; linarith
  · exact h

/-! ### Consequences for the choice of `a` -/

/-- An additional copy has a point of `P_a` of rank below `ℓ` or above `r`. -/
lemma bad (hc : C σ a Θ) (hne : Finset.univ.image Θ ≠ canon σ) :
    (∃ s : ℕ, 1 ≤ s ∧ s < lv σ ∧ thInv σ Θ s ∈ Pa428 σ a) ∨
      (∃ s : ℕ, rv σ < s ∧ s ≤ k ∧ thInv σ Θ s ∈ Pa428 σ a) := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl', hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  have hlr := hc.lr
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  apply hne
  apply copy_D419_eq hc.standing hc.lt
  refine ⟨hc.copy.1, fun i => Or.resolve_right (hc.copy.2 i) ?_⟩
  intro hi
  have hr := sval_range σ (i := i.val + 1) (by omega) (by have := i.isLt; omega)
  rw [← th_fin Θ i, th_eq_thInv σ Θ (by omega) (by have := i.isLt; omega)] at hi
  set j := sval σ (i.val + 1)
  rcases lt_trichotomy j (lv σ) with hj | hj | hj
  · exact h1 j hr.1 hj hi
  · rw [hj, thInv_eq_th σ Θ (by omega) (by omega), hsl'] at hi; exact (c432 hc).1 hi
  · rcases eq_or_lt_of_le (show rv σ ≤ j by omega) with hj' | hj'
    · rw [← hj', thInv_eq_th σ Θ (by omega) (by omega), hsr] at hi; exact (c432 hc).2 hi
    · exact h2 j hj' hr.2 hi

/-- With `a = u - 1`, a bad copy with a low rank on `P_a` forces `u < σ⁻¹(ℓ-1) < σ⁻¹(k-1)`. -/
lemma low_um1 (hc : C σ a Θ) (ha : a + 1 = up σ)
    (hs : ∃ s : ℕ, 1 ≤ s ∧ s < lv σ ∧ thInv σ Θ s ∈ Pa428 σ a) :
    up σ < spos σ (lv σ - 1) ∧ spos σ (lv σ - 1) < spos σ (k - 1) := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl', hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  have hlr := hc.lr
  have hR := hc.copy.1
  obtain ⟨-, -, hsh⟩ := c433_1 hc hs
  obtain ⟨-, hxk, -⟩ := c434_1 hc hs
  obtain ⟨s, hs1, hsl, hsP⟩ := hs
  have hP := Pa_props (c436 hc ⟨hs1, hsl⟩ hsP (lv σ - 1) (by omega) (by omega))
  have hk1 := hsh (k - 1) (by omega) le_rfl
  rw [show k - 1 + 1 = k by omega, sigInv_eq σ (by omega) le_rfl] at hk1
  have hua : (up σ : ℝ) = a + 1 := by rw [← ha]; push_cast; ring
  constructor
  · have := (thInv_x_lt_iff hR (j := k) (j' := lv σ - 1) (by omega) le_rfl (by omega)
      (by omega)).1 (by linarith [hP.1])
    unfold up; exact this
  · refine (thInv_x_lt_iff hR (j := lv σ - 1) (j' := k - 1) (by omega) (by omega) (by omega)
      (by omega)).1 ?_
    rw [hk1]; simp only; unfold up at hua; linarith [hP.2.1]

/-- With `a = k - 2`, a bad copy with a low rank on `P_a` forces `σ⁻¹(k-1) < σ⁻¹(ℓ-1)` when
`u ≤ k - 2`. A step inside Lemma 4.29's proof by contradiction for the choice `a = k - 2` under
(4.18) (tex l.1417, l.1429): its hypotheses can never all hold (they contradict Claims 4.33, 4.34
and 4.36, `UG.c433_1`, `UG.c434_1`, `UG.c436`), so it holds only vacuously. Used only inside
`UG.uniq_km2`, to reach a contradiction from a copy `Θ ≠ Σ`. -/
lemma low_km2 (hc : C σ a Θ) (ha : a + 2 = k) (hu : up σ + 2 ≤ k)
    (hs : ∃ s : ℕ, 1 ≤ s ∧ s < lv σ ∧ thInv σ Θ s ∈ Pa428 σ a) :
    spos σ (k - 1) < spos σ (lv σ - 1) := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl', hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  have hlr := hc.lr
  have hR := hc.copy.1
  obtain ⟨-, -, hsh⟩ := c433_1 hc hs
  obtain ⟨s, hs1, hsl, hsP⟩ := hs
  have hP := Pa_props (c436 hc ⟨hs1, hsl⟩ hsP (lv σ - 1) (by omega) (by omega))
  have hk1 := hsh (k - 1) (by omega) le_rfl
  rw [show k - 1 + 1 = k by omega, sigInv_eq σ (by omega) le_rfl] at hk1
  have hua : (up σ : ℝ) ≤ a := by
    have : up σ ≤ a := by omega
    exact_mod_cast this
  refine (thInv_x_lt_iff hR (j := k - 1) (j' := lv σ - 1) (by omega) (by omega) (by omega)
    (by omega)).1 ?_
  rw [hk1]; simp only; unfold up at hua; linarith [hP.1]

/-- With `a = b`, a bad copy with a high rank on `P_a` forces `σ⁻¹(2) < σ⁻¹(r+1) < b`. -/
lemma high_b (hc : C σ a Θ) (ha : a = bp σ)
    (hs : ∃ s : ℕ, rv σ < s ∧ s ≤ k ∧ thInv σ Θ s ∈ Pa428 σ a) :
    spos σ 2 < spos σ (rv σ + 1) ∧ spos σ (rv σ + 1) < bp σ := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl', hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  have hlr := hc.lr
  have hR := hc.copy.1
  obtain ⟨-, -, hsh⟩ := c433_2 hc hs
  obtain ⟨-, hx1, -⟩ := c434_2 hc hs
  obtain ⟨s, hs1, hsk, hsP⟩ := hs
  have hP := Pa_props (c436m hc ⟨hs1, hsk⟩ hsP (rv σ + 1) (by omega) (by omega))
  have h2 := hsh 2 le_rfl (by omega)
  rw [sigInv_eq σ le_rfl (by omega)] at h2
  have hba : (bp σ : ℝ) = a := by rw [ha]
  constructor
  · refine (thInv_x_lt_iff hR (j := 2) (j' := rv σ + 1) (by omega) (by omega) (by omega)
      (by omega)).1 ?_
    rw [h2]; simp only; unfold bp at hba; linarith [hP.1]
  · have := (thInv_x_lt_iff hR (j := rv σ + 1) (j' := 1) (by omega) (by omega) le_rfl
      (by omega)).1 (by linarith [hP.2.1])
    unfold bp; exact this

/-- With `a = 2`, a bad copy with a high rank on `P_a` forces `σ⁻¹(r+1) < σ⁻¹(2)` when
`b ≥ 3`. A step inside Lemma 4.29's proof by contradiction for the mirror choice `a = 2` under
(4.19) (tex l.1382, l.1431): its hypotheses can never all hold (they contradict the mirror images of
Claims 4.33, 4.34 and 4.36), so it holds only vacuously. Used only inside `UG.uniq_2`, to reach a
contradiction from a copy `Θ ≠ Σ`. -/
lemma high_2 (hc : C σ a Θ) (ha : a = 2) (hb : 3 ≤ bp σ)
    (hs : ∃ s : ℕ, rv σ < s ∧ s ≤ k ∧ thInv σ Θ s ∈ Pa428 σ a) :
    spos σ (rv σ + 1) < spos σ 2 := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, hsl', hsr, hvb, hvu⟩ := facts hc.standing hc.lr
  have hlr := hc.lr
  have hR := hc.copy.1
  obtain ⟨-, -, hsh⟩ := c433_2 hc hs
  obtain ⟨s, hs1, hsk, hsP⟩ := hs
  have hP := Pa_props (c436m hc ⟨hs1, hsk⟩ hsP (rv σ + 1) (by omega) (by omega))
  have h2 := hsh 2 le_rfl (by omega)
  rw [sigInv_eq σ le_rfl (by omega)] at h2
  have hba : (a : ℝ) + 1 ≤ bp σ := by
    have : a + 1 ≤ bp σ := by omega
    exact_mod_cast this
  refine (thInv_x_lt_iff hR (j := rv σ + 1) (j' := 2) (by omega) (by omega) (by omega)
    (by omega)).1 ?_
  rw [h2]; simp only; unfold bp at hba; linarith [hP.2.1]


end Ctx

/-! ### The two-block exclusion and the choices of `a` -/

section Choice

variable {σ : Perm (Fin k)}

/-- Under the standing hypotheses and `ℓ + 1 = r`, (UD), (BD) and `b < u` cannot hold together:
they would force `σ` to be a two-block pattern of Subsection 4.1, which `Standing44` excludes. The
proof uses `Standing44.not41` but not `Standing44.not42`; the paper states the latter (tex l.1018),
and it is kept to match the paper. -/
lemma not_UD_BD (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ)
    (hU : ∀ j : ℕ, rv σ ≤ j → j < k → spos σ (j + 1) < spos σ j)
    (hB : ∀ j : ℕ, 1 ≤ j → j < lv σ → spos σ (j + 1) < spos σ j) (hbu : bp σ < up σ) :
    False := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu', hsl', hsr, hvb, hvu⟩ := facts hσ hlr
  set ℓ := lv σ with hℓ
  -- lower bound on the positions of `1, …, ℓ`
  have hA : ∀ j, 1 ≤ j → j ≤ ℓ → ℓ + 1 ≤ spos σ j + j := by
    refine down_ind (fun j => ℓ + 1 ≤ spos σ j + j) (by omega) ?_
    intro s hs1 hsl ih
    have := hB (s - 1) (by omega) (by omega)
    rw [show s - 1 + 1 = s by omega] at this
    omega
  have hb : ℓ ≤ bp σ := by have := hA 1 le_rfl (by omega); unfold bp; omega
  -- upper bound on the positions of `r, …, k`
  have hC : ∀ j, rv σ ≤ j → j ≤ k → spos σ j + j ≤ k + rv σ := by
    refine up_ind (fun j => spos σ j + j ≤ k + rv σ) (by omega) ?_
    intro s hrs hsk ih
    have := hU s hrs hsk
    omega
  have hu : up σ ≤ rv σ := by have := hC k (by omega) le_rfl; unfold up; omega
  have hbl : bp σ = ℓ := by omega
  have hul : up σ = ℓ + 1 := by omega
  have hA' : ∀ j, 1 ≤ j → j ≤ ℓ → spos σ j + j ≤ ℓ + 1 := by
    refine up_ind (fun j => spos σ j + j ≤ ℓ + 1) (by unfold bp at hbl; omega) ?_
    intro s hs1 hsl ih
    have := hB s hs1 hsl
    omega
  have hC' : ∀ j, 1 ≤ j → j ≤ k → rv σ ≤ j → k + rv σ ≤ spos σ j + j := by
    refine down_ind (fun j => rv σ ≤ j → k + rv σ ≤ spos σ j + j) ?_ ?_
    · intro _; unfold up at hul; omega
    · intro s hs1 hsk ih hrs
      have := hU (s - 1) hrs (by omega)
      rw [show s - 1 + 1 = s by omega] at this
      have := ih (by omega)
      omega
  apply hσ.not41
  refine Or.inl ⟨ℓ, by omega, by omega, ?_⟩
  intro i hi1 hik
  split_ifs with hil
  · have h1 := hA (ℓ + 1 - i) (by omega) (by omega)
    have h2 := hA' (ℓ + 1 - i) (by omega) (by omega)
    have he : spos σ (ℓ + 1 - i) = i := by omega
    have := sval_spos σ (j := ℓ + 1 - i) (by omega) (by omega)
    rw [he] at this; exact this
  · have h1 := hC (k + ℓ + 1 - i) (by omega) (by omega)
    have h2 := hC' (k + ℓ + 1 - i) (by omega) (by omega) (by omega)
    have he : spos σ (k + ℓ + 1 - i) = i := by omega
    have := sval_spos σ (j := k + ℓ + 1 - i) (by omega) (by omega)
    rw [he] at this; exact this

/-- If no additional copy exists in `D_a`, the conclusion of Lemma 4.29 holds for `a`. -/
lemma unique_of {a : ℕ} (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ) (ha : 2 ≤ a ∧ a ≤ k - 2)
    (H : ∀ Θ : Fin k → ℝ × ℝ, C σ a Θ → Finset.univ.image Θ ≠ canon σ → False) :
    ∀ P : Finset (ℝ × ℝ), (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
      (↑P : Set (ℝ × ℝ)) ⊆ D428 σ a → IsUniqueCopy σ ↑P := by
  intro P h1 h2
  refine ⟨h1, fun Θ hΘ => ?_⟩
  by_contra hne
  exact H Θ ⟨hσ, hlr, ha, hΘ.1, fun i => h2 (hΘ.2 i)⟩ hne

/-- If (BD) fails, `b < u`, and (4.18) fails, then `a = u - 1` works. (This is the case (UD),
not (BD) of the proof of Lemma 4.29, but (UD) itself is not needed.) -/
lemma uniq_um1' (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ) (hbu : bp σ < up σ)
    (hBD : ¬ (∀ j : ℕ, 1 ≤ j → j < lv σ → spos σ (j + 1) < spos σ j))
    (hA : ¬ (up σ < spos σ (lv σ - 1) ∧ spos σ (lv σ - 1) < spos σ (k - 1))) :
    ∀ P : Finset (ℝ × ℝ), (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
      (↑P : Set (ℝ × ℝ)) ⊆ D428 σ (up σ - 1) → IsUniqueCopy σ ↑P := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, -⟩ := facts hσ hlr
  refine unique_of hσ hlr ⟨by omega, by omega⟩ fun Θ hc hne => ?_
  rcases bad hc hne with hs | hs
  · exact hA (low_um1 hc (by omega) hs)
  · exact hBD (c434_2 hc hs).1

/-- Specific choice (iii): under not (BD) and (4.18), `a = k - 2` works. -/
lemma uniq_km2 (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ)
    (hBD : ¬ (∀ j : ℕ, 1 ≤ j → j < lv σ → spos σ (j + 1) < spos σ j))
    (hpq : up σ < spos σ (lv σ - 1) ∧ spos σ (lv σ - 1) < spos σ (k - 1)) :
    ∀ P : Finset (ℝ × ℝ), (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
      (↑P : Set (ℝ × ℝ)) ⊆ D428 σ (k - 2) → IsUniqueCopy σ ↑P := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, -⟩ := facts hσ hlr
  have hq := spos_range σ (j := k - 1) (by omega) (by omega)
  refine unique_of hσ hlr ⟨by omega, le_rfl⟩ fun Θ hc hne => ?_
  rcases bad hc hne with hs | hs
  · have := low_km2 hc (by omega) (by omega) hs; omega
  · exact hBD (c434_2 hc hs).1

/-- Mirror of (iii): under not (UD) and (4.19), `a = 2` works. -/
lemma uniq_2 (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ)
    (hUD : ¬ (∀ j : ℕ, rv σ ≤ j → j < k → spos σ (j + 1) < spos σ j))
    (hpq : spos σ 2 < spos σ (rv σ + 1) ∧ spos σ (rv σ + 1) < bp σ) :
    ∀ P : Finset (ℝ × ℝ), (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
      (↑P : Set (ℝ × ℝ)) ⊆ D428 σ 2 → IsUniqueCopy σ ↑P := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, -⟩ := facts hσ hlr
  have hq := spos_range σ (j := 2) (by omega) (by omega)
  refine unique_of hσ hlr ⟨le_rfl, by omega⟩ fun Θ hc hne => ?_
  rcases bad hc hne with hs | hs
  · exact hUD (c434_1 hc hs).1
  · have := high_2 hc rfl (by omega) hs; omega

/-- Mirror of the case `a = u - 1`: under not (UD), `b < u` and not (4.19), `a = b` works. -/
lemma uniq_b (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ) (hbu : bp σ < up σ)
    (hUD : ¬ (∀ j : ℕ, rv σ ≤ j → j < k → spos σ (j + 1) < spos σ j))
    (hB : ¬ (spos σ 2 < spos σ (rv σ + 1) ∧ spos σ (rv σ + 1) < bp σ)) :
    ∀ P : Finset (ℝ × ℝ), (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
      (↑P : Set (ℝ × ℝ)) ⊆ D428 σ (bp σ) → IsUniqueCopy σ ↑P := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, -⟩ := facts hσ hlr
  refine unique_of hσ hlr ⟨hb2, by omega⟩ fun Θ hc hne => ?_
  rcases bad hc hne with hs | hs
  · exact hUD (c434_1 hc hs).1
  · exact hB (high_b hc rfl hs)

end Choice

end UG

/-- The context of the proof of Lemma 4.29 (tex l.1265): the standing hypotheses, `ℓ = r - 1`,
a fixed `a ∈ {2, …, k-2}`, and a `σ`-copy `Θ ⊆ D_a` with `Θ ≠ Σ`. -/
structure Ctx429 (σ : Perm (Fin k)) (a : ℕ) (Θ : Fin k → ℝ × ℝ) : Prop where
  standing : Standing44 σ
  lr : lv σ + 1 = rv σ
  ha : 2 ≤ a ∧ a ≤ k - 2
  copy : CopyIn σ Θ (D428 σ a)
  ne : Finset.univ.image Θ ≠ canon σ

/-- `Ctx429` without the field `ne` is the auxiliary context `UG.C`. -/
theorem UG.C.ofCtx {σ : Perm (Fin k)} {a : ℕ} {Θ : Fin k → ℝ × ℝ} (hc : Ctx429 σ a Θ) :
    UG.C σ a Θ :=
  ⟨hc.standing, hc.lr, hc.ha, hc.copy⟩

/-- **Claim 4.30** (propagation away from `P_a`), statements 1–4:
1. if `j < k`, `Θ⁻¹(j) ∉ P_a` and `Θ⁻¹(j)_y > j`, then `Θ⁻¹(j+1)_y > j+1`;
2. if `j > 1`, `Θ⁻¹(j) ∉ P_a` and `Θ⁻¹(j)_y < j`, then `Θ⁻¹(j-1)_y < j-1`;
3. if `i < k`, `Θ(i) ∉ P_a` and `Θ(i)_x > i`, then `Θ(i+1)_x > i+1`;
4. if `i > 1`, `Θ(i) ∉ P_a` and `Θ(i)_x < i`, then `Θ(i-1)_x < i-1`.

Its proof does not use `ne` (`Θ ≠ Σ`) or `Standing44.not41`/`not42` (tex l.1018); these paper
hypotheses are kept to match the paper. Unlike the contexts of Lemmas 4.5, 4.10, 4.13, 4.20 and
4.40, the context `Ctx429` (a fixed `a`, tex l.1265) can be satisfied, e.g. by `σ = (31254)`,
`a = 2`. -/
theorem claim_4_30 (σ : Perm (Fin k)) (a : ℕ) (Θ : Fin k → ℝ × ℝ) (hc : Ctx429 σ a Θ) :
    (∀ j : ℕ, 1 ≤ j → j < k → thInv σ Θ j ∉ Pa428 σ a → (j : ℝ) < (thInv σ Θ j).2 →
      ((j : ℝ) + 1) < (thInv σ Θ (j + 1)).2) ∧
    (∀ j : ℕ, 1 < j → j ≤ k → thInv σ Θ j ∉ Pa428 σ a → (thInv σ Θ j).2 < (j : ℝ) →
      (thInv σ Θ (j - 1)).2 < (j : ℝ) - 1) ∧
    (∀ i : ℕ, 1 ≤ i → i < k → th Θ i ∉ Pa428 σ a → (i : ℝ) < (th Θ i).1 →
      ((i : ℝ) + 1) < (th Θ (i + 1)).1) ∧
    (∀ i : ℕ, 1 < i → i ≤ k → th Θ i ∉ Pa428 σ a → (th Θ i).1 < (i : ℝ) →
      (th Θ (i - 1)).1 < (i : ℝ) - 1) :=
  ⟨UG.c430_1 (UG.C.ofCtx hc), UG.c430_2 (UG.C.ofCtx hc), UG.c430_3 (UG.C.ofCtx hc),
    UG.c430_4 (UG.C.ofCtx hc)⟩

/-- **Corollary 4.31**, statements 1–4:
1. if `Θ⁻¹(j)_y > j` and `Θ⁻¹(j)_y ≥ ℓ + 1`, then `Θ⁻¹(s)_y > s` for `j ≤ s ≤ k`;
2. if `Θ⁻¹(j)_y < j` and `Θ⁻¹(j)_y ≤ ℓ`, then `Θ⁻¹(s)_y < s` for `1 ≤ s ≤ j`;
3. if `Θ(i)_x > i` and `Θ(i)_x ≥ a + 1`, then `Θ(s)_x > s` for `i ≤ s ≤ k`;
4. if `Θ(i)_x < i` and `Θ(i)_x ≤ a`, then `Θ(s)_x < s` for `1 ≤ s ≤ i`.

Its proof does not use `ne` (`Θ ≠ Σ`) or `Standing44.not41`/`not42` (tex l.1018); these paper
hypotheses are kept to match the paper. Unlike the contexts of Lemmas 4.5, 4.10, 4.13, 4.20 and
4.40, the context `Ctx429` (a fixed `a`, tex l.1265) can be satisfied, e.g. by `σ = (31254)`,
`a = 2`. -/
theorem cor_4_31 (σ : Perm (Fin k)) (a : ℕ) (Θ : Fin k → ℝ × ℝ) (hc : Ctx429 σ a Θ) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k → (j : ℝ) < (thInv σ Θ j).2 → (lv σ : ℝ) + 1 ≤ (thInv σ Θ j).2 →
      ∀ s : ℕ, j ≤ s → s ≤ k → (s : ℝ) < (thInv σ Θ s).2) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ k → (thInv σ Θ j).2 < (j : ℝ) → (thInv σ Θ j).2 ≤ (lv σ : ℝ) →
      ∀ s : ℕ, 1 ≤ s → s ≤ j → (thInv σ Θ s).2 < (s : ℝ)) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ k → (i : ℝ) < (th Θ i).1 → (a : ℝ) + 1 ≤ (th Θ i).1 →
      ∀ s : ℕ, i ≤ s → s ≤ k → (s : ℝ) < (th Θ s).1) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ k → (th Θ i).1 < (i : ℝ) → (th Θ i).1 ≤ (a : ℝ) →
      ∀ s : ℕ, 1 ≤ s → s ≤ i → (th Θ s).1 < (s : ℝ)) :=
  ⟨fun j hj1 _ => UG.c431_1 (UG.C.ofCtx hc) j hj1,
    fun j _ hjk => UG.c431_2 (UG.C.ofCtx hc) j hjk,
    fun i hi1 _ => UG.c431_3 (UG.C.ofCtx hc) i hi1,
    fun i _ hik => UG.c431_4 (UG.C.ofCtx hc) i hik⟩

/-- **Claim 4.32.** `Θ(1) ∉ P_a` and `Θ(k) ∉ P_a`.

Its proof does not use `ne` (`Θ ≠ Σ`) or `Standing44.not42` (tex l.1018); these paper
hypotheses are kept to match the paper. Unlike the contexts of Lemmas 4.5, 4.10, 4.13, 4.20 and
4.40, the context `Ctx429` (a fixed `a`, tex l.1265) can be satisfied, e.g. by `σ = (31254)`,
`a = 2`. -/
theorem claim_4_32 (σ : Perm (Fin k)) (a : ℕ) (Θ : Fin k → ℝ × ℝ) (hc : Ctx429 σ a Θ) :
    th Θ 1 ∉ Pa428 σ a ∧ th Θ k ∉ Pa428 σ a :=
  UG.c432 (UG.C.ofCtx hc)

/-- **Claim 4.33.**
1. If `Θ⁻¹(s) ∈ P_a` for some `s < ℓ`, then `Θ⁻¹(ℓ)_y ≥ ℓ + 1`, `Θ⁻¹(k) ∈ P_U`, and
   `Θ⁻¹(j) = Σ⁻¹(j+1)` for `r ≤ j ≤ k - 1` (4.13);
2. if `Θ⁻¹(s) ∈ P_a` for some `s > r`, then `Θ⁻¹(r)_y ≤ ℓ`, `Θ⁻¹(1) ∈ P_B`, and
   `Θ⁻¹(j) = Σ⁻¹(j-1)` for `2 ≤ j ≤ ℓ` (4.14).

Its proof does not use `ne` (`Θ ≠ Σ`) or `Standing44.not42` (tex l.1018); these paper
hypotheses are kept to match the paper. Unlike the contexts of Lemmas 4.5, 4.10, 4.13, 4.20 and
4.40, the context `Ctx429` (a fixed `a`, tex l.1265) can be satisfied, e.g. by `σ = (31254)`,
`a = 2`. -/
theorem claim_4_33 (σ : Perm (Fin k)) (a : ℕ) (Θ : Fin k → ℝ × ℝ) (hc : Ctx429 σ a Θ) :
    ((∃ s : ℕ, 1 ≤ s ∧ s < lv σ ∧ thInv σ Θ s ∈ Pa428 σ a) →
      (lv σ : ℝ) + 1 ≤ (thInv σ Θ (lv σ)).2 ∧ thInv σ Θ k ∈ PU419 σ ∧
      ∀ j : ℕ, rv σ ≤ j → j ≤ k - 1 → thInv σ Θ j = sigInv σ (j + 1)) ∧
    ((∃ s : ℕ, rv σ < s ∧ s ≤ k ∧ thInv σ Θ s ∈ Pa428 σ a) →
      (thInv σ Θ (rv σ)).2 ≤ (lv σ : ℝ) ∧ thInv σ Θ 1 ∈ PB419 σ ∧
      ∀ j : ℕ, 2 ≤ j → j ≤ lv σ → thInv σ Θ j = sigInv σ (j - 1)) :=
  ⟨UG.c433_1 (UG.C.ofCtx hc), UG.c433_2 (UG.C.ofCtx hc)⟩

/-- Condition (UD): `σ⁻¹(k) < σ⁻¹(k-1) < ⋯ < σ⁻¹(r+1) < σ⁻¹(r)`. -/
def UD (σ : Perm (Fin k)) : Prop := ∀ j : ℕ, rv σ ≤ j → j < k → spos σ (j + 1) < spos σ j

/-- Condition (BD): `σ⁻¹(ℓ) < σ⁻¹(ℓ-1) < ⋯ < σ⁻¹(2) < σ⁻¹(1)`. -/
def BD (σ : Perm (Fin k)) : Prop := ∀ j : ℕ, 1 ≤ j → j < lv σ → spos σ (j + 1) < spos σ j

/-- **Claim 4.34.**
1. If `Θ⁻¹(s) ∈ P_a` for some `s < ℓ`, then (UD) holds, `Θ⁻¹(k)_x < u - 1`, and `b < u`;
2. if `Θ⁻¹(s) ∈ P_a` for some `s > r`, then (BD) holds, `Θ⁻¹(1)_x > b + 1`, and `b < u`.

Its proof does not use `ne` (`Θ ≠ Σ`) or `Standing44.not42` (tex l.1018); these paper
hypotheses are kept to match the paper. Unlike the contexts of Lemmas 4.5, 4.10, 4.13, 4.20 and
4.40, the context `Ctx429` (a fixed `a`, tex l.1265) can be satisfied, e.g. by `σ = (31254)`,
`a = 2`. -/
theorem claim_4_34 (σ : Perm (Fin k)) (a : ℕ) (Θ : Fin k → ℝ × ℝ) (hc : Ctx429 σ a Θ) :
    ((∃ s : ℕ, 1 ≤ s ∧ s < lv σ ∧ thInv σ Θ s ∈ Pa428 σ a) →
      UD σ ∧ (thInv σ Θ k).1 < (up σ : ℝ) - 1 ∧ bp σ < up σ) ∧
    ((∃ s : ℕ, rv σ < s ∧ s ≤ k ∧ thInv σ Θ s ∈ Pa428 σ a) →
      BD σ ∧ (bp σ : ℝ) + 1 < (thInv σ Θ 1).1 ∧ bp σ < up σ) :=
  ⟨UG.c434_1 (UG.C.ofCtx hc), UG.c434_2 (UG.C.ofCtx hc)⟩

/-- **Corollary 4.35.** Under the standing hypotheses and `ℓ = r - 1`: if `b > u`, or if neither
(UD) nor (BD) holds, then every `a ∈ {2, …, k-2}` satisfies the conclusion of Lemma 4.29. The proof
does not use the premise `IsPermPointSet P` (tex l.1255) or `Standing44.not42` (tex l.1018); the
paper states both, and they are kept to match the paper. -/
theorem cor_4_35 (σ : Perm (Fin k)) (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ)
    (hcase : up σ < bp σ ∨ (¬ UD σ ∧ ¬ BD σ)) :
    ∀ a : ℕ, 2 ≤ a → a ≤ k - 2 →
      ∀ P : Finset (ℝ × ℝ), IsPermPointSet P → (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
        (↑P : Set (ℝ × ℝ)) ⊆ D428 σ a → IsUniqueCopy σ ↑P := by
  intro a ha2 hak P _
  refine UG.unique_of hσ hlr ⟨ha2, hak⟩ (fun Θ hc hne => ?_) P
  rcases UG.bad hc hne with hs | hs
  · obtain ⟨hU, -, hbu⟩ := UG.c434_1 hc hs
    rcases hcase with h | h
    · omega
    · exact h.1 hU
  · obtain ⟨hB, -, hbu⟩ := UG.c434_2 hc hs
    rcases hcase with h | h
    · omega
    · exact h.2 hB

/-- **Claim 4.36.** In the case where (UD) holds and (BD) fails: if `Θ⁻¹(s) ∈ P_a` for some
`s < ℓ`, then `Θ⁻¹(t) ∈ P_a` for `s ≤ t < ℓ`.

Its proof does not use `ne` (`Θ ≠ Σ`), nor `Standing44.not42` (tex l.1018), nor the binders `hUD`
and `hBD`, the paper's case "(UD) holds and (BD) fails" (tex l.1382); these paper hypotheses are
kept to match the paper. The context `Ctx429` (a fixed `a`, tex l.1265) can be satisfied, e.g. by
`σ = (31254)`, `a = 2`. -/
theorem claim_4_36 (σ : Perm (Fin k)) (a : ℕ) (Θ : Fin k → ℝ × ℝ) (hc : Ctx429 σ a Θ)
    (hUD : UD σ) (hBD : ¬ BD σ) (s : ℕ) (hs : 1 ≤ s ∧ s < lv σ)
    (hsP : thInv σ Θ s ∈ Pa428 σ a) :
    ∀ t : ℕ, s ≤ t → t < lv σ → thInv σ Θ t ∈ Pa428 σ a :=
  UG.c436 (UG.C.ofCtx hc) hs hsP

namespace UG

/-! ### The specific choices of `a` made in the proof of Lemma 4.29 (tex l.1409–1419)

These are used by Corollaries 4.37 and 4.38 and by Lemma 4.40. -/

variable {σ : Perm (Fin k)}

/-- (i) If `b = u - 1` and neither exceptional configuration of Corollary 4.37 occurs, then the
choice `a = u - 1 = b` gives uniqueness in `D_a`. -/
theorem choice_um1 (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ) (hbu : bp σ + 1 = up σ)
    (hA : ¬ (UD σ ∧ ¬ BD σ ∧ up σ < spos σ (lv σ - 1) ∧ spos σ (lv σ - 1) < spos σ (k - 1)))
    (hB : ¬ (BD σ ∧ ¬ UD σ ∧ spos σ 2 < spos σ (rv σ + 1) ∧ spos σ (rv σ + 1) < bp σ)) :
    ∀ P : Finset (ℝ × ℝ), (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
      (↑P : Set (ℝ × ℝ)) ⊆ D428 σ (up σ - 1) → IsUniqueCopy σ ↑P := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, -⟩ := facts hσ hlr
  refine unique_of hσ hlr ⟨by omega, by omega⟩ fun Θ hc hne => ?_
  rcases bad hc hne with hs | hs
  · obtain ⟨hU, -, hbu'⟩ := c434_1 hc hs
    have hpq := low_um1 hc (by omega) hs
    by_cases hBD : BD σ
    · exact not_UD_BD hσ hlr hU hBD hbu'
    · exact hA ⟨hU, hBD, hpq⟩
  · obtain ⟨hBD, -, hbu'⟩ := c434_2 hc hs
    have hpq := high_b hc (by omega) hs
    by_cases hU : UD σ
    · exact not_UD_BD hσ hlr hU hBD hbu'
    · exact hB ⟨hBD, hU, hpq⟩

/-- (ii) If `b > u`, every `a ∈ {2, …, k-2}` gives uniqueness in `D_a` (Corollary 4.35). The proof
does not use the premise `IsPermPointSet P`; the paper states it (tex l.1255), and it is kept to
match the paper. -/
theorem choice_gt (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ) (hub : up σ < bp σ) :
    ∀ a : ℕ, 2 ≤ a → a ≤ k - 2 →
      ∀ P : Finset (ℝ × ℝ), IsPermPointSet P → (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
        (↑P : Set (ℝ × ℝ)) ⊆ D428 σ a → IsUniqueCopy σ ↑P :=
  cor_4_35 σ hσ hlr (Or.inl hub)

/-- The proof of Lemma 4.29. It does not use the premise `IsPermPointSet P`; the paper states it
(tex l.1255), and it is kept to match the paper. -/
lemma lemma429 (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ) :
    ∃ a : ℕ, 2 ≤ a ∧ a ≤ k - 2 ∧
      ∀ P : Finset (ℝ × ℝ), IsPermPointSet P → (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
        (↑P : Set (ℝ × ℝ)) ⊆ D428 σ a → IsUniqueCopy σ ↑P := by
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, -⟩ := facts hσ hlr
  by_cases hlt : bp σ < up σ
  · by_cases hU : UD σ <;> by_cases hB : BD σ
    · exact absurd (not_UD_BD hσ hlr hU hB hlt) id
    · by_cases hpq : up σ < spos σ (lv σ - 1) ∧ spos σ (lv σ - 1) < spos σ (k - 1)
      · exact ⟨k - 2, by omega, le_rfl, fun P _ => uniq_km2 hσ hlr hB hpq P⟩
      · exact ⟨up σ - 1, by omega, by omega, fun P _ => uniq_um1' hσ hlr hlt hB hpq P⟩
    · by_cases hpq : spos σ 2 < spos σ (rv σ + 1) ∧ spos σ (rv σ + 1) < bp σ
      · exact ⟨2, le_rfl, by omega, fun P _ => uniq_2 hσ hlr hU hpq P⟩
      · exact ⟨bp σ, hb2, by omega, fun P _ => uniq_b hσ hlr hlt hU hpq P⟩
    · exact ⟨2, le_rfl, by omega, cor_4_35 σ hσ hlr (Or.inr ⟨hU, hB⟩) 2 le_rfl (by omega)⟩
  · exact ⟨2, le_rfl, by omega, cor_4_35 σ hσ hlr (Or.inl (by omega)) 2 le_rfl (by omega)⟩

end UG

/-- **Lemma 4.29.** Under the standing hypotheses of Subsection 4.4 and `ℓ = r - 1`, there is
`a ∈ {2, …, k-2}` such that every point set `Π` associated with a permutation with
`Σ ⊆ Π ⊆ D_a` has `Σ` as its unique `σ`-copy. The proof does not use the premise `IsPermPointSet P`
(tex l.1255) or `Standing44.not42` (tex l.1018); the paper states both, and they are kept to match
the paper. -/
theorem lemma_4_29 (σ : Perm (Fin k)) (hσ : Standing44 σ) (hlr : lv σ + 1 = rv σ) :
    ∃ a : ℕ, 2 ≤ a ∧ a ≤ k - 2 ∧
      ∀ P : Finset (ℝ × ℝ), IsPermPointSet P → (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
        (↑P : Set (ℝ × ℝ)) ⊆ D428 σ a → IsUniqueCopy σ ↑P :=
  UG.lemma429 hσ hlr

namespace UG37

/-! ### Stripe coverage for Corollaries 4.37 and 4.38 (tex l.1227, l.1435–1438) -/

open DISC

variable {k : ℕ}

/-- A unit piece of a closed segment lying in a horizontal stripe. -/
lemma cover_H {S : Set (ℝ × ℝ)} (A V : ℝ × ℝ) (T : ℝ) (s i : ℕ) (hV1 : V.1 ≠ 0)
    (hV2 : V.2 ≠ 0) (hs : (s : ℝ) + 1 ≤ T) (h1 : (i : ℝ) ≤ A.2 + s * V.2)
    (h2 : A.2 + s * V.2 ≤ (i : ℝ) + 1) (h3 : (i : ℝ) ≤ A.2 + s * V.2 + 1 * V.2)
    (h4 : A.2 + s * V.2 + 1 * V.2 ≤ (i : ℝ) + 1)
    (hS : ∀ p ∈ closedSeg A V T, p ∈ hStripe i → p ∈ S) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ S ∧ openSeg a v ⊆ hStripe i := by
  have hH : openSeg (A.1 + s * V.1, A.2 + s * V.2) (1 * V.1, 1 * V.2) ⊆ hStripe i :=
    openSeg_subset_hStripe _ _ i (by simpa using hV2) h1 h2 h3 h4
  have hC := openSeg_subset_closedSeg A V s 1 T (Nat.cast_nonneg s) zero_le_one hs
  exact ⟨_, _, by simpa using hV1, by simpa using hV2, fun p hp => hS p (hC hp) (hH hp), hH⟩

/-- A unit piece of a closed segment lying in a vertical stripe. -/
lemma cover_V {S : Set (ℝ × ℝ)} (A V : ℝ × ℝ) (T : ℝ) (s i : ℕ) (hV1 : V.1 ≠ 0)
    (hV2 : V.2 ≠ 0) (hs : (s : ℝ) + 1 ≤ T) (h1 : (i : ℝ) ≤ A.1 + s * V.1)
    (h2 : A.1 + s * V.1 ≤ (i : ℝ) + 1) (h3 : (i : ℝ) ≤ A.1 + s * V.1 + 1 * V.1)
    (h4 : A.1 + s * V.1 + 1 * V.1 ≤ (i : ℝ) + 1)
    (hS : ∀ p ∈ closedSeg A V T, p ∈ vStripe i → p ∈ S) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ S ∧ openSeg a v ⊆ vStripe i := by
  have hH : openSeg (A.1 + s * V.1, A.2 + s * V.2) (1 * V.1, 1 * V.2) ⊆ vStripe i :=
    openSeg_subset_vStripe _ _ i (by simpa using hV1) h1 h2 h3 h4
  have hC := openSeg_subset_closedSeg A V s 1 T (Nat.cast_nonneg s) zero_le_one hs
  exact ⟨_, _, by simpa using hV1, by simpa using hV2, fun p hp => hS p (hC hp) (hH hp), hH⟩

/-- The segment `(x₀, 1) + t(e, 1)`, `0 ≤ t ≤ k-1`, meets every `H_i`. -/
lemma diag_up {S : Set (ℝ × ℝ)} (x0 e : ℝ) (he : e ≠ 0) {i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k)
    (hS : ∀ p ∈ closedSeg (x0, 1) (e, 1) ((k : ℝ) - 1), p ∈ hStripe i → p ∈ S) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ S ∧ openSeg a v ⊆ hStripe i := by
  obtain ⟨s, rfl⟩ : ∃ s, i = s + 1 := ⟨i - 1, by omega⟩
  have hk : (s : ℝ) + 1 + 1 ≤ k := by exact_mod_cast hik
  refine cover_H (x0, 1) (e, 1) _ s (s + 1) he one_ne_zero (by linarith) ?_ ?_ ?_ ?_ hS <;>
    push_cast <;> linarith

/-- The segment `(x₀, k) + t(e, -1)`, `0 ≤ t ≤ k-1`, meets every `H_i`. -/
lemma diag_down {S : Set (ℝ × ℝ)} (x0 e : ℝ) (he : e ≠ 0) {i : ℕ} (hi : 1 ≤ i)
    (hik : i + 1 ≤ k)
    (hS : ∀ p ∈ closedSeg (x0, (k : ℝ)) (e, -1) ((k : ℝ) - 1), p ∈ hStripe i → p ∈ S) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ S ∧ openSeg a v ⊆ hStripe i := by
  obtain ⟨s, rfl⟩ : ∃ s, k = i + 1 + s := ⟨k - (i + 1), by omega⟩
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  refine cover_H _ (e, -1) _ s i he (by norm_num) (by push_cast; linarith) ?_ ?_ ?_ ?_ hS <;>
    push_cast <;> linarith

/-- The segment `(1, y₀) + t(1, e)`, `0 ≤ t ≤ k-1`, meets every `V_i`. -/
lemma diag_right {S : Set (ℝ × ℝ)} (y0 e : ℝ) (he : e ≠ 0) {i : ℕ} (hi : 1 ≤ i)
    (hik : i + 1 ≤ k)
    (hS : ∀ p ∈ closedSeg (1, y0) (1, e) ((k : ℝ) - 1), p ∈ vStripe i → p ∈ S) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ S ∧ openSeg a v ⊆ vStripe i := by
  obtain ⟨s, rfl⟩ : ∃ s, i = s + 1 := ⟨i - 1, by omega⟩
  have hk : (s : ℝ) + 1 + 1 ≤ k := by exact_mod_cast hik
  refine cover_V (1, y0) (1, e) _ s (s + 1) one_ne_zero he (by linarith) ?_ ?_ ?_ ?_ hS <;>
    push_cast <;> linarith

/-- The segment `(k, y₀) + t(-1, e)`, `0 ≤ t ≤ k-1`, meets every `V_i`. -/
lemma diag_left {S : Set (ℝ × ℝ)} (y0 e : ℝ) (he : e ≠ 0) {i : ℕ} (hi : 1 ≤ i)
    (hik : i + 1 ≤ k)
    (hS : ∀ p ∈ closedSeg ((k : ℝ), y0) (-1, e) ((k : ℝ) - 1), p ∈ vStripe i → p ∈ S) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ S ∧ openSeg a v ⊆ vStripe i := by
  obtain ⟨s, rfl⟩ : ∃ s, k = i + 1 + s := ⟨k - (i + 1), by omega⟩
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  refine cover_V _ (-1, e) _ s i (by norm_num) he (by push_cast; linarith) ?_ ?_ ?_ ?_ hS <;>
    push_cast <;> linarith

variable {σ : Perm (Fin k)}

/-- Under `ℓ < r`, `P_L` meets `H_i` for `ℓ + 1 ≤ i ≤ k - 1`. -/
lemma PL_cover (hlr : lv σ < rv σ) {i : ℕ} (h1 : lv σ + 1 ≤ i) (h2 : i + 1 ≤ k) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ PL419 σ ∧ openSeg a v ⊆ hStripe i := by
  have hS : ∀ p, p ∈ IL419 σ → p ∈ hStripe i → p ∈ PL419 σ := by
    intro p hp hH
    refine ⟨⟨hp, notMem_lattice_of_hStripe hH⟩, ?_⟩
    simp only [hlr, ↓reduceIte]
    have : (lv σ : ℝ) + 1 ≤ i := by exact_mod_cast h1
    linarith [hH.1]
  unfold IL419 at hS
  split_ifs at hS
  · exact diag_up 1 (-1) (by norm_num) (by omega) h2 hS
  · exact diag_down 1 (-1) (by norm_num) (by omega) h2 hS

/-- Under `ℓ < r`, `P_R` meets `H_i` for `1 ≤ i ≤ r - 2`. -/
lemma PR_cover (hlr : lv σ < rv σ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i + 2 ≤ rv σ) (h3 : i + 1 ≤ k) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ PR419 σ ∧ openSeg a v ⊆ hStripe i := by
  have hS : ∀ p, p ∈ IR419 σ → p ∈ hStripe i → p ∈ PR419 σ := by
    intro p hp hH
    refine ⟨⟨hp, notMem_lattice_of_hStripe hH⟩, ?_⟩
    simp only [hlr, ↓reduceIte]
    have : (i : ℝ) + 2 ≤ rv σ := by exact_mod_cast h2
    linarith [hH.2]
  unfold IR419 at hS
  split_ifs at hS
  · exact diag_up _ 1 one_ne_zero h1 h3 hS
  · exact diag_down _ 1 one_ne_zero h1 h3 hS

/-- `P_B` meets `V_i` for `b + 1 ≤ i ≤ k - 1` when `b < u`. -/
lemma PB_cover_lt (hbu : bp σ < up σ) {i : ℕ} (h1 : bp σ + 1 ≤ i) (h2 : i + 1 ≤ k) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ PB419 σ ∧ openSeg a v ⊆ vStripe i := by
  have hS : ∀ p, p ∈ IB419 σ → p ∈ vStripe i → p ∈ PB419 σ := by
    intro p hp hH
    refine ⟨⟨hp, notMem_lattice_of_vStripe hH⟩, ?_⟩
    simp only [hbu, ↓reduceIte]
    have : (bp σ : ℝ) + 1 ≤ i := by exact_mod_cast h1
    linarith [hH.1]
  unfold IB419 at hS
  split_ifs at hS
  · exact diag_right 1 (-1) (by norm_num) (by omega) h2 hS
  · exact diag_left 1 (-1) (by norm_num) (by omega) h2 hS

/-- `P_B` meets `V_i` for `1 ≤ i ≤ b - 2` when `b > u`. -/
lemma PB_cover_gt (hbu : ¬ bp σ < up σ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i + 2 ≤ bp σ)
    (h3 : i + 1 ≤ k) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ PB419 σ ∧ openSeg a v ⊆ vStripe i := by
  have hS : ∀ p, p ∈ IB419 σ → p ∈ vStripe i → p ∈ PB419 σ := by
    intro p hp hH
    refine ⟨⟨hp, notMem_lattice_of_vStripe hH⟩, ?_⟩
    simp only [hbu, ↓reduceIte]
    have : (i : ℝ) + 2 ≤ bp σ := by exact_mod_cast h2
    linarith [hH.2]
  unfold IB419 at hS
  split_ifs at hS
  · exact diag_right 1 (-1) (by norm_num) h1 h3 hS
  · exact diag_left 1 (-1) (by norm_num) h1 h3 hS

/-- `P_U` meets `V_i` for `1 ≤ i ≤ u - 2` when `b < u`. -/
lemma PU_cover_lt (hbu : bp σ < up σ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i + 2 ≤ up σ)
    (h3 : i + 1 ≤ k) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ PU419 σ ∧ openSeg a v ⊆ vStripe i := by
  have hS : ∀ p, p ∈ IU419 σ → p ∈ vStripe i → p ∈ PU419 σ := by
    intro p hp hH
    refine ⟨⟨hp, notMem_lattice_of_vStripe hH⟩, ?_⟩
    simp only [hbu, ↓reduceIte]
    have : (i : ℝ) + 2 ≤ up σ := by exact_mod_cast h2
    linarith [hH.2]
  unfold IU419 at hS
  split_ifs at hS
  · exact diag_right _ 1 one_ne_zero h1 h3 hS
  · exact diag_left _ 1 one_ne_zero h1 h3 hS

/-- `P_U` meets `V_i` for `u + 1 ≤ i ≤ k - 1` when `b > u`. -/
lemma PU_cover_gt (hbu : ¬ bp σ < up σ) {i : ℕ} (h1 : up σ + 1 ≤ i) (h2 : i + 1 ≤ k) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ PU419 σ ∧ openSeg a v ⊆ vStripe i := by
  have hS : ∀ p, p ∈ IU419 σ → p ∈ vStripe i → p ∈ PU419 σ := by
    intro p hp hH
    refine ⟨⟨hp, notMem_lattice_of_vStripe hH⟩, ?_⟩
    simp only [hbu, ↓reduceIte]
    have : (up σ : ℝ) + 1 ≤ i := by exact_mod_cast h1
    linarith [hH.1]
  unfold IU419 at hS
  split_ifs at hS
  · exact diag_right _ 1 one_ne_zero (by omega) h2 hS
  · exact diag_left _ 1 one_ne_zero (by omega) h2 hS

/-- Monotonicity of the coverage witness in the support. -/
lemma mono {S S' St : Set (ℝ × ℝ)} (h : S ⊆ S')
    (hc : ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ S ∧ openSeg a v ⊆ St) :
    ∃ a v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a v ⊆ S' ∧ openSeg a v ⊆ St := by
  obtain ⟨a, v, h1, h2, h3, h4⟩ := hc
  exact ⟨a, v, h1, h2, h3.trans h, h4⟩

/-- Under `ℓ = r - 1`, the support `D_a` covers every horizontal stripe `H_i`, `1 ≤ i ≤ k - 1`:
it contains a non-axis-parallel open segment inside `H_i`, taken from `P_R` (`i < ℓ`), `P_a`
(`i = ℓ`) or `P_L` (`i > ℓ`) (tex l.1227). -/
lemma H_cover (hlr : lv σ + 1 = rv σ) (a : ℕ) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ k - 1) :
    ∃ a' v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a' v ⊆ D428 σ a ∧
      openSeg a' v ⊆ hStripe i := by
  have hlt : lv σ < rv σ := by omega
  rcases lt_trichotomy i (lv σ) with h | h | h
  · exact mono (fun p hp => UG.mem_D428.2 (Or.inr (Or.inr (Or.inl hp))))
      (PR_cover hlt h1 (by omega) (by omega))
  · subst h
    refine ⟨((a : ℝ), (lv σ : ℝ)), (1, 1), one_ne_zero, one_ne_zero,
      fun p hp => UG.mem_D428.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp))))), ?_⟩
    exact openSeg_subset_hStripe _ _ _ one_ne_zero (by simp) (by simp) (by simp) (by simp)
  · exact mono (fun p hp => UG.mem_D428.2 (Or.inr (Or.inl hp))) (PL_cover hlt h (by omega))

/-- Under the stated case conditions, the support `D_a` covers the vertical stripe `V_i`: it
contains a non-axis-parallel open segment inside `V_i`, taken from `P_B`, `P_U` or `P_a`. -/
lemma V_cover (a : ℕ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i + 1 ≤ k)
    (hlt : bp σ < up σ → i = a ∨ bp σ + 1 ≤ i ∨ i + 2 ≤ up σ)
    (hgt : ¬ bp σ < up σ → i = a ∨ i + 2 ≤ bp σ ∨ up σ + 1 ≤ i) :
    ∃ a' v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a' v ⊆ D428 σ a ∧
      openSeg a' v ⊆ vStripe i := by
  have hB : PB419 σ ⊆ D428 σ a := fun p hp => UG.mem_D428.2 (Or.inr (Or.inr (Or.inr (Or.inl hp))))
  have hU : PU419 σ ⊆ D428 σ a :=
    fun p hp => UG.mem_D428.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))
  have hPa : ∃ a' v : ℝ × ℝ, v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ openSeg a' v ⊆ D428 σ a ∧
      openSeg a' v ⊆ vStripe a :=
    ⟨((a : ℝ), (lv σ : ℝ)), (1, 1), one_ne_zero, one_ne_zero,
      fun p hp => UG.mem_D428.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp))))),
      openSeg_subset_vStripe _ _ _ one_ne_zero (by simp) (by simp) (by simp) (by simp)⟩
  by_cases hbu : bp σ < up σ
  · rcases hlt hbu with h | h | h
    · subst h; exact hPa
    · exact mono hB (PB_cover_lt hbu h h2)
    · exact mono hU (PU_cover_lt hbu h1 h h2)
  · rcases hgt hbu with h | h | h
    · subst h; exact hPa
    · exact mono hB (PB_cover_gt hbu h1 h h2)
    · exact mono hU (PU_cover_gt hbu h h2)

/-- Discretization for the support `D_a` of Construction 4.28. -/
lemma geom_of (hlr : lv σ + 1 = rv σ) (a : ℕ)
    (hV : ∀ i, 1 ≤ i → i + 1 ≤ k → (bp σ < up σ → i = a ∨ bp σ + 1 ≤ i ∨ i + 2 ≤ up σ) ∧
      (¬ bp σ < up σ → i = a ∨ i + 2 ≤ bp σ ∨ up σ + 1 ≤ i))
    (huniq : ∀ P : Finset (ℝ × ℝ), IsPermPointSet P → (↑(canon σ) : Set (ℝ × ℝ)) ⊆ ↑P →
      (↑P : Set (ℝ × ℝ)) ⊆ D428 σ a → IsUniqueCopy σ ↑P) :
    GeomConclusion σ (N0 k) := by
  obtain ⟨hk2, -⟩ := UG.lr_facts hlr
  refine geomConclusion_of_segs' σ hk2 (D428 σ a) (UG.canon_subset_D428 a)
    (fun i h1 h2 => H_cover hlr a h1 h2) (fun i h1 h2 => ?_) huniq
  obtain ⟨hA, hB⟩ := hV i h1 (by omega)
  exact V_cover a h1 (by omega) hA hB

end UG37

/-- **Corollary 4.37.** Under the standing hypotheses, assume `ℓ = r - 1`. Then Theorem 4.1 holds
for `σ` unless `b = u - 1` and one of the following occurs:
(a) (UD) holds, (BD) fails, and `u < σ⁻¹(ℓ-1) < σ⁻¹(k-1)` (4.18);
(b) (BD) holds, (UD) fails, and `σ⁻¹(2) < σ⁻¹(r+1) < b` (4.19).
As in Theorem 4.1, the threshold `N₀(k)` depends only on `k`: one threshold works for every such
pattern of length `k`. The proof does not use `Standing44.not42`; the paper states it (tex l.1018),
and it is kept to match the paper. -/
theorem cor_4_37 (k : ℕ) :
    ∃ N₀ : ℕ, ∀ σ : Perm (Fin k), Standing44 σ → lv σ + 1 = rv σ →
      ¬ (bp σ + 1 = up σ ∧
        ((UD σ ∧ ¬ BD σ ∧ up σ < spos σ (lv σ - 1) ∧ spos σ (lv σ - 1) < spos σ (k - 1)) ∨
         (BD σ ∧ ¬ UD σ ∧ spos σ 2 < spos σ (rv σ + 1) ∧ spos σ (rv σ + 1) < bp σ))) →
      GeomConclusion σ N₀ := by
  refine ⟨DISC.N0 k, fun σ hσ hlr hexc => ?_⟩
  obtain ⟨hk4, hl2, hrk, hb2, hbk, hu2, huk, hbu, -⟩ := UG.facts hσ hlr
  rcases (show bp σ + 2 ≤ up σ ∨ up σ + 2 ≤ bp σ ∨ bp σ = up σ + 1 ∨ bp σ + 1 = up σ by omega)
    with h | h | h | h
  · -- `|b - u| ≥ 2`: Lemma 4.29's `a`; `P_B`, `P_U` cover every vertical stripe.
    obtain ⟨a, -, -, hu⟩ := lemma_4_29 σ hσ hlr
    exact UG37.geom_of hlr a (fun i _ _ => ⟨fun _ => by omega, fun _ => by omega⟩) hu
  · obtain ⟨a, -, -, hu⟩ := lemma_4_29 σ hσ hlr
    exact UG37.geom_of hlr a (fun i _ _ => ⟨fun _ => by omega, fun _ => by omega⟩) hu
  · -- `b = u + 1`: `a = u` (Corollary 4.35); `P_a` covers `H_ℓ` and `V_u`.
    exact UG37.geom_of hlr (up σ) (fun i _ _ => ⟨fun _ => by omega, fun _ => by omega⟩)
      (UG.choice_gt hσ hlr (by omega) (up σ) hu2 (by omega))
  · -- `b = u - 1`: `a = u - 1 = b` unless (4.18)/(4.19); `P_a` covers `H_ℓ` and `V_b`.
    have hu := UG.choice_um1 hσ hlr h (fun hA => hexc ⟨h, Or.inl hA⟩)
      (fun hB => hexc ⟨h, Or.inr hB⟩)
    rw [show up σ - 1 = bp σ by omega] at hu
    exact UG37.geom_of hlr (bp σ) (fun i _ _ => ⟨fun _ => by omega, fun _ => by omega⟩)
      (fun P _ => hu P)

/-- Condition (LD): `σ(1) > σ(2) > ⋯ > σ(b-1) > σ(b)`. -/
def LD (σ : Perm (Fin k)) : Prop := ∀ i : ℕ, 1 ≤ i → i < bp σ → sval σ (i + 1) < sval σ i

/-- Condition (RD): `σ(u) > σ(u+1) > ⋯ > σ(k-1) > σ(k)`. -/
def RD (σ : Perm (Fin k)) : Prop := ∀ i : ℕ, up σ ≤ i → i < k → sval σ (i + 1) < sval σ i

/-- **Corollary 4.38.** Under the standing hypotheses, assume `b = u - 1`. Then Theorem 4.1 holds
for `σ` unless `ℓ = r - 1` and one of the following occurs:
(a) (LD) holds, (RD) fails, and `σ(2) < σ(u+1) < ℓ` (4.20);
(b) (RD) holds, (LD) fails, and `r < σ(b-1) < σ(k-1)` (4.21).
As in Theorem 4.1, the threshold `N₀(k)` depends only on `k`: one threshold works for every such
pattern of length `k`. The proof uses `Standing44.not42` only to pass it on to the reflected
pattern `antiD σ` when it builds `Standing44 (antiD σ)` for Corollary 4.37, which does not need it;
with the field deleted (and that line removed) the proof still compiles. The paper states the
hypothesis (tex l.1018), and it is kept to match the paper. -/
theorem cor_4_38 (k : ℕ) :
    ∃ N₀ : ℕ, ∀ σ : Perm (Fin k), Standing44 σ → bp σ + 1 = up σ →
      ¬ (lv σ + 1 = rv σ ∧
        ((LD σ ∧ ¬ RD σ ∧ sval σ 2 < sval σ (up σ + 1) ∧ sval σ (up σ + 1) < lv σ) ∨
         (RD σ ∧ ¬ LD σ ∧ rv σ < sval σ (bp σ - 1) ∧ sval σ (bp σ - 1) < sval σ (k - 1)))) →
      GeomConclusion σ N₀ := by
  -- Corollary 4.37 applied to the anti-diagonal reflection `antiD σ` (tex l.1458–1462).
  obtain ⟨N₀, hN⟩ := cor_4_37 k
  refine ⟨N₀, fun σ hσ hbu hexc => DISC.geomConclusion_of_antiD ?_⟩
  have hk : 1 ≤ k := by
    by_contra h0
    have := DISC.sval_le σ 1
    exact hσ.l_ne.2 (by unfold lv; omega)
  have hb1 := (DISC.bp_eq_one_iff σ).not.2 hσ.l_ne.1
  have hbk := (DISC.bp_eq_k_iff σ hk).not.2 hσ.r_ne.1
  have hu1 := (DISC.up_eq_one_iff σ hk).not.2 hσ.l_ne.2
  have huk := (DISC.up_eq_k_iff σ hk).not.2 hσ.r_ne.2
  have hb0 : 1 ≤ bp σ := DISC.one_le_spos σ le_rfl hk
  have hbk' : bp σ ≤ k := DISC.spos_le σ 1
  have hu0 : 1 ≤ up σ := DISC.one_le_spos σ hk le_rfl
  have huk' : up σ ≤ k := DISC.spos_le σ k
  have hl0 : 1 ≤ lv σ := DISC.one_le_sval σ le_rfl hk
  have hlk : lv σ ≤ k := DISC.sval_le σ 1
  have hr0 : 1 ≤ rv σ := DISC.one_le_sval σ hk le_rfl
  have hrk : rv σ ≤ k := DISC.sval_le σ k
  have hlA := DISC.lv_antiD σ hk
  have hrA := DISC.rv_antiD σ hk
  have hbA := DISC.bp_antiD σ hk
  have huA := DISC.up_antiD σ hk
  have hσ' : Standing44 (DISC.antiD σ) :=
    ⟨fun h => hσ.not41 ((DISC.isTwoBlock_antiD_iff σ).1 h),
      fun h => hσ.not42 ((DISC.isExcFive_antiD_iff σ).1 h),
      ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  refine hN (DISC.antiD σ) hσ' (by omega) ?_
  rintro ⟨hbu', hcase⟩
  have hUD : UD (DISC.antiD σ) ↔ LD σ := DISC.ud_antiD_iff σ
  have hBD : BD (DISC.antiD σ) ↔ RD σ := DISC.bd_antiD_iff σ
  have s2 := DISC.sval_le σ 2
  have sk1 := DISC.sval_le σ (k - 1)
  have su1 := DISC.sval_le σ (up σ + 1)
  have sb1 := DISC.sval_le σ (bp σ - 1)
  refine hexc ⟨by omega, ?_⟩
  rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · have e1 := DISC.spos_antiD σ (j := lv (DISC.antiD σ) - 1) (by omega) (by omega)
    have e2 := DISC.spos_antiD σ (j := k - 1) (by omega) (by omega)
    rw [show k + 1 - (lv (DISC.antiD σ) - 1) = up σ + 1 by omega] at e1
    rw [show k + 1 - (k - 1) = 2 by omega] at e2
    rw [e1, e2] at h4
    rw [e1] at h3
    exact Or.inl ⟨hUD.1 h1, fun h => h2 (hBD.2 h), by omega, by omega⟩
  · have e1 := DISC.spos_antiD σ (j := rv (DISC.antiD σ) + 1) (by omega) (by omega)
    have e2 := DISC.spos_antiD σ (j := 2) (by omega) (by omega)
    rw [show k + 1 - (rv (DISC.antiD σ) + 1) = bp σ - 1 by omega] at e1
    rw [show k + 1 - 2 = k - 1 by omega] at e2
    rw [e1, e2] at h3
    rw [e1] at h4
    exact Or.inr ⟨hBD.1 h1, fun h => h2 (hUD.2 h), by omega, by omega⟩

end LinfPermRemoval
