import RequestProject.ProofImports
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite counting for sparse systems of binary equalities

The estimates here use only finite sets. A family of constraints, each involving
at most `K` variables and with each variable in at most `D` constraints, has a
pairwise variable-disjoint subfamily of size at least a `1 / (K*D)` fraction.
-/

namespace AneVsAn.BinarySeparation

set_option autoImplicit false

open Finset
open scoped Classical

/-- A binary term is either a fixed bit or one random bit. -/
abbrev BitTerm (V : Type*) := Bool ⊕ V

def BitTerm.eval {V : Type*} : BitTerm V → (V → Bool) → Bool
  | Sum.inl b, _ => b
  | Sum.inr v, a => a v

def BitTerm.vars {V : Type*} [DecidableEq V] : BitTerm V → Finset V
  | Sum.inl _ => ∅
  | Sum.inr v => {v}

theorem BitTerm.exists_pivot {V : Type*} [DecidableEq V] (l r : BitTerm V)
    (hne : (l.vars ∪ r.vars).Nonempty) (hdiff : l ≠ r) :
    ∃ v ∈ l.vars ∪ r.vars,
      ∀ a b : V → Bool, l.eval a = r.eval a → l.eval b = r.eval b →
        (∀ w ∈ l.vars ∪ r.vars, w ≠ v → a w = b w) → a v = b v := by
  cases l with
  | inl x =>
    cases r with
    | inl y => simp [BitTerm.vars] at hne
    | inr v =>
      refine ⟨v, by simp [BitTerm.vars], ?_⟩
      intro a b ha hb _
      simpa [BitTerm.eval] using ha.symm.trans hb
  | inr v =>
    cases r with
    | inl x =>
      refine ⟨v, by simp [BitTerm.vars], ?_⟩
      intro a b ha hb _
      simpa [BitTerm.eval] using ha.trans hb.symm
    | inr w =>
      have hvw : v ≠ w := by intro h; subst w; exact hdiff rfl
      refine ⟨v, by simp [BitTerm.vars], ?_⟩
      intro a b ha hb heq
      have hw := heq w (by simp [BitTerm.vars]) (Ne.symm hvw)
      simpa [BitTerm.eval] using ha.trans (hw.trans hb.symm)

theorem exists_disjoint_supports {I V : Type*} [DecidableEq I] [DecidableEq V]
    (s : Finset I) (support : I → Finset V) (K D : ℕ)
    (hne : ∀ i ∈ s, (support i).Nonempty)
    (hsize : ∀ i ∈ s, (support i).card ≤ K)
    (hdegree : ∀ v, (s.filter (fun i => v ∈ support i)).card ≤ D) :
    ∃ t : Finset I, t ⊆ s ∧
      (t : Set I).Pairwise (fun i j => Disjoint (support i) (support j)) ∧
      s.card ≤ K * D * t.card := by
  classical
  let candidates := s.powerset.filter
    (fun t : Finset I => (t : Set I).Pairwise (fun i j => Disjoint (support i) (support j)))
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨t, ht, hmax⟩ := candidates.exists_max_image Finset.card hcandidates
  have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have htp : (t : Set I).Pairwise (fun i j => Disjoint (support i) (support j)) :=
    (Finset.mem_filter.mp ht).2
  have hhit : ∀ i ∈ s, ∃ j ∈ t, ¬Disjoint (support j) (support i) := by
    intro i hi
    by_contra hh
    push_neg at hh
    have hit : i ∉ t := by
      intro hit
      obtain ⟨v, hv⟩ := hne i hi
      exact Finset.disjoint_left.mp (hh i hit) hv hv
    have hins : insert i t ∈ candidates := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hi
        · exact hts hj
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with hai | hat
        · rcases Finset.mem_insert.mp hb with hbi | hbt
          · exact (hab (hai.trans hbi.symm)).elim
          · simpa [hai] using (hh b hbt).symm
        · rcases Finset.mem_insert.mp hb with hbi | hbt
          · simpa [hbi] using hh a hat
          · exact htp hat hbt hab
    have hcard := hmax (insert i t) hins
    rw [Finset.card_insert_of_notMem hit] at hcard
    omega
  let near := fun j => s.filter (fun i => ¬Disjoint (support j) (support i))
  have hnear : ∀ j ∈ t, (near j).card ≤ K * D := by
    intro j hj
    have hsub : near j ⊆ (support j).biUnion
        (fun v => s.filter (fun i => v ∈ support i)) := by
      intro i hi
      obtain ⟨his, hd⟩ := Finset.mem_filter.mp hi
      obtain ⟨v, hvj, hvi⟩ := Finset.not_disjoint_iff.mp hd
      exact Finset.mem_biUnion.mpr ⟨v, hvj, Finset.mem_filter.mpr ⟨his, hvi⟩⟩
    calc
      (near j).card ≤ ((support j).biUnion
          (fun v => s.filter (fun i => v ∈ support i))).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ support j, (s.filter (fun i => v ∈ support i)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ support j, D := Finset.sum_le_sum (fun v _ => hdegree v)
      _ = (support j).card * D := by simp
      _ ≤ K * D := Nat.mul_le_mul_right D (hsize j (hts hj))
  have hcover : s ⊆ t.biUnion near := by
    intro i hi
    obtain ⟨j, hj, hji⟩ := hhit i hi
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hi, hji⟩⟩
  refine ⟨t, hts, htp, ?_⟩
  calc
    s.card ≤ (t.biUnion near).card := Finset.card_le_card hcover
    _ ≤ ∑ j ∈ t, (near j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ t, K * D := Finset.sum_le_sum hnear
    _ = K * D * t.card := by simp [Nat.mul_comm]

/-- A constraint determines its pivot once the other variables in its support
are specified. Disjoint supports therefore remove one binary degree of freedom
per constraint. -/
theorem card_solutions_le_of_disjoint_supports {I V : Type*}
    [DecidableEq I] [DecidableEq V] [Fintype V]
    (s : Finset I) (support : I → Finset V) (pivot : I → V)
    (C : I → (V → Bool) → Prop)
    (hpivot : ∀ i ∈ s, pivot i ∈ support i)
    (hdisj : (s : Set I).Pairwise (fun i j => Disjoint (support i) (support j)))
    (hdet : ∀ i ∈ s, ∀ a b : V → Bool, C i a → C i b →
      (∀ v ∈ support i, v ≠ pivot i → a v = b v) → a (pivot i) = b (pivot i)) :
    (Finset.univ.filter (fun a : V → Bool => ∀ i ∈ s, C i a)).card ≤
      2 ^ (Fintype.card V - s.card) := by
  classical
  let P := s.image pivot
  have hinj : Set.InjOn pivot s := by
    intro i hi j hj hij
    by_contra hne
    have hd := hdisj hi hj hne
    exact Finset.disjoint_left.mp hd (hpivot i hi) (hij ▸ hpivot j hj)
  have hPcard : P.card = s.card := Finset.card_image_of_injOn hinj
  let restrict : {a : V → Bool // ∀ i ∈ s, C i a} → ({v : V // v ∉ P} → Bool) :=
    fun a v => a.val v.val
  have hrestrict : Function.Injective restrict := by
    intro a b hab
    apply Subtype.ext
    funext v
    have heq : ∀ v, v ∉ P → a.val v = b.val v := by
      intro v hv
      exact congrFun hab ⟨v, hv⟩
    by_cases hv : v ∈ P
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      apply hdet i hi a.val b.val (a.property i hi) (b.property i hi)
      intro v hv hvi
      apply heq v
      intro hvP
      obtain ⟨j, hj, hpj⟩ := Finset.mem_image.mp hvP
      by_cases hij : i = j
      · subst j
        exact hvi hpj.symm
      · have hd := hdisj hi hj hij
        exact Finset.disjoint_left.mp hd hv (hpj ▸ hpivot j hj)
    · exact heq v hv
  have hcard := Fintype.card_le_of_injective restrict hrestrict
  have hrest : Fintype.card {v : V // v ∉ P} = Fintype.card V - s.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hPcard]
  simpa only [Fintype.card_subtype, Fintype.card_fun, Fintype.card_bool, hrest] using hcard

/-- The elementary finite union bound, expressed without probability. -/
theorem exists_avoiding_all {I A : Type*} [Fintype I] [Fintype A]
    (C : I → A → Prop) (R : ℕ)
    (hC : ∀ i, (Finset.univ.filter (C i)).card ≤ R)
    (hsize : Fintype.card I * R < Fintype.card A) :
    ∃ a, ∀ i, ¬C i a := by
  classical
  by_contra h
  push_neg at h
  have hcover : (Finset.univ : Finset A) ⊆
      Finset.univ.biUnion (fun i => Finset.univ.filter (C i)) := by
    intro a _
    obtain ⟨i, hi⟩ := h a
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hi]⟩
  have hle : Fintype.card A ≤ Fintype.card I * R := by
    calc
      Fintype.card A = (Finset.univ : Finset A).card := by simp
      _ ≤ (Finset.univ.biUnion (fun i => Finset.univ.filter (C i))).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ i : I, (Finset.univ.filter (C i)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : I, R := Finset.sum_le_sum (fun i _ => hC i)
      _ = Fintype.card I * R := by simp
  omega

end AneVsAn.BinarySeparation
