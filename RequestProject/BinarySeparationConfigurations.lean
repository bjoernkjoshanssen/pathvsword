import RequestProject.BinarySeparationCount
import RequestProject.GenericLoops

/-!
# Reduction to a long loop or a confined two-cycle

The sharper state budget makes the five configurations in the manuscript
unnecessary as a separate classification. Any loop confined to the run already
has one of four possible pairs of endpoints. If there is no such loop, the run
alternates between two states that occur nowhere else.
-/

namespace AneVsAn.BinarySeparation

open AneVsAn.Generic

set_option autoImplicit false

variable {L : ℕ} {S : Type} [DecidableEq S] {u : ℕ → Bool} {c : ℕ → S}

def LongRunLoop (L : ℕ) (c : ℕ → S) : Prop :=
  ∃ a r, LoopBlock (3 * L + 1) c a r ∧ L ≤ a ∧ a ≤ L + 1 ∧
    2 * L ≤ a + r ∧ a + r ≤ 2 * L + 1

def ConfinedTwoCycle (L : ℕ) (c : ℕ → S) : Prop :=
  c L ≠ c (L + 1) ∧
    (∀ t, t ≤ 3 * L + 1 → (c t = c L ∨ c t = c (L + 1)) →
      L ≤ t ∧ t ≤ 2 * L + 1) ∧
    (∀ i, i ≤ L + 1 → c (L + i) = if i % 2 = 0 then c L else c (L + 1))

theorem rvis_eq_visitTimes {s : S} (hs : s ∈ cluster L c) :
    rvis L c s = visitTimes (3 * L + 1) c s := by
  have hs' := (mem_cluster_iff.mp hs).2
  ext t
  rw [mem_rvis_iff, mem_visitTimes]
  constructor
  · rintro ⟨ht, ht', he⟩
    exact ⟨by omega, he⟩
  · rintro ⟨ht, he⟩
    exact ⟨(hs' t ht he).1, (hs' t ht he).2, he⟩

theorem long_run_loop_of_adjacent
    (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2)
    {t : ℕ} (ht : t < 3 * L + 1) (he : c t = c (t + 1))
    (hc : c t ∈ cluster L c) : LongRunLoop L c := by
  obtain ⟨a, r, hl, hca, _, _⟩ := loopBlock_of_adjacent huaw ht he
  have hr := hl.1
  have hn := hl.2.1
  have hconf := (mem_cluster_iff.mp hc).2
  have ha := hconf a (by omega) hca
  have hlast := hconf (a + r) hn
    (((hl.2.2 (a + r) hn).2 ⟨by omega, le_rfl⟩).trans hca)
  have hcount := loop_card huaw hl
  exact ⟨a, r, hl, ha.1, by omega, by omega, hlast.2⟩

theorem long_run_loop_of_one_cluster (hL : 6 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2)
    (hc : (cluster L c).card = 1) : LongRunLoop L c := by
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hc
  have hsmem : s ∈ cluster L c := by rw [hs]; simp
  have hrvis : L ≤ (rvis L c s).card := by
    have hh := clusterVisits_ge (by omega) houter hcard
    simpa only [clusterVisits, hs, Finset.sum_singleton] using hh
  rw [rvis_eq_visitTimes hsmem] at hrvis
  obtain ⟨a, p, hp, hn, hvis, _, _⟩ := visits_progression huaw s (by omega)
  set v := (visitTimes (3 * L + 1) c s).card with hv
  have hfirst : c a = s := by
    apply (hvis a (by omega)).2
    exact ⟨0, by omega, by simp⟩
  have hlast : c (a + (v - 1) * p) = s := by
    apply (hvis (a + (v - 1) * p) hn).2
    exact ⟨v - 1, by omega, rfl⟩
  have hconf := (mem_cluster_iff.mp hsmem).2
  have ha := hconf a (by omega) hfirst
  have hb := hconf (a + (v - 1) * p) hn hlast
  have hmul := Nat.mul_le_mul_right p (show L - 1 ≤ v - 1 by omega)
  have hp1 : p = 1 := by
    by_contra hpne
    have hmul2 := Nat.mul_le_mul_left (L - 1) (show 2 ≤ p by omega)
    have hsub : L - 1 + 1 = L := by omega
    nlinarith
  subst p
  have hnext : c (a + 1) = s := by
    apply (hvis (a + 1) (by omega)).2
    exact ⟨1, by omega, by simp⟩
  have hacluster : c a ∈ cluster L c := by rw [hfirst]; exact hsmem
  exact long_run_loop_of_adjacent huaw hcard (by omega) (hfirst.trans hnext.symm) hacluster

theorem confined_two_cycle_of_no_adjacent (hL : 1 ≤ L)
    (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2)
    (hc : (cluster L c).card = 2)
    (hneq : ∀ t, L ≤ t → t < 2 * L + 1 → c t ≠ c (t + 1)) :
    ConfinedTwoCycle L c := by
  have hm := (cluster_two_budget houter hcard hc).1
  have hmem (t : ℕ) (ht : L ≤ t) (ht' : t ≤ 2 * L + 1) : c t ∈ cluster L c :=
    run_state_mem_cluster_of_no_mixed houter hm ht ht'
  have hdiff := hneq L le_rfl (by omega)
  have hcl : cluster L c = {c L, c (L + 1)} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact hmem L le_rfl (by omega)
      · exact hmem (L + 1) (by omega) (by omega)
    · simp [hc, hdiff]
  have hinside (t : ℕ) (ht : L ≤ t) (ht' : t ≤ 2 * L + 1) :
      c t = c L ∨ c t = c (L + 1) := by
    have hh := hmem t ht ht'
    simpa only [hcl, Finset.mem_insert, Finset.mem_singleton] using hh
  refine ⟨hdiff, ?_, ?_⟩
  · intro t ht h
    rcases h with h | h
    · exact (mem_cluster_iff.mp (hmem L le_rfl (by omega))).2 t ht h
    · exact (mem_cluster_iff.mp (hmem (L + 1) (by omega) (by omega))).2 t ht h
  · intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hdiff' := hneq (L + i) (by omega) (by omega)
      have hnext := hinside (L + (i + 1)) (by omega) (by omega)
      have hindex : L + i + 1 = L + (i + 1) := by omega
      rw [hindex] at hdiff'
      by_cases heven : i % 2 = 0
      · have hodd : (i + 1) % 2 ≠ 0 := by omega
        simp only [if_pos heven] at hprev
        simp only [if_neg hodd]
        rcases hnext with hnext | hnext
        · exact False.elim (hdiff' (hprev.trans hnext.symm))
        · exact hnext
      · have heven' : (i + 1) % 2 = 0 := by omega
        simp only [if_neg heven] at hprev
        simp only [if_pos heven']
        rcases hnext with hnext | hnext
        · exact hnext
        · exact False.elim (hdiff' (hprev.trans hnext.symm))

theorem run_configuration (hL : 6 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2) :
    LongRunLoop L c ∨ ConfinedTwoCycle L c := by
  rcases cluster_card_cases (by omega) houter hcard with hc | hc
  · exact Or.inl (long_run_loop_of_one_cluster hL huaw houter hcard hc)
  · by_cases ha : ∃ t, L ≤ t ∧ t < 2 * L + 1 ∧ c t = c (t + 1)
    · obtain ⟨t, ht, ht', he⟩ := ha
      have hm := (cluster_two_budget houter hcard hc).1
      have hmem := run_state_mem_cluster_of_no_mixed houter hm ht (by omega)
      exact Or.inl (long_run_loop_of_adjacent huaw hcard (by omega) he hmem)
    · have hneq : ∀ t, L ≤ t → t < 2 * L + 1 → c t ≠ c (t + 1) := by
        intro t ht ht' he
        exact ha ⟨t, ht, ht', he⟩
      exact Or.inr (confined_two_cycle_of_no_adjacent (by omega) houter hcard hc hneq)

end AneVsAn.BinarySeparation
