import RequestProject.BinaryLower

/-!
# The binary example, second half: `A_N(1101000000100) = 7`

This file computes the *unique* nondeterministic automatic complexity
(Definition 1.1, `def:complexities`, of `anevsanseparationv4.tex`) of the same binary
word

`w = 1101000000100`

of length `13` whose *exact* complexity was shown to be `6` in
`RequestProject/BinaryLower.lean`: it is `7`.  Together with `ANe_eq_six` this gives a
fully formal instance of the separation `A_{Ne}(w) < A_N(w)` studied in the source
(Theorem 1.2, `thm:main`, proves that such words exist of arbitrarily large length; the
word here is a single small witness of the same phenomenon).

## Outline

The argument follows the one of `RequestProject/BinaryLower.lean`, with exact acceptance
replaced by unique acceptance.

* Any NFA with `q` states uniquely accepting `w` has an accepting path `c 0, …, c 13`.
  Deleting every transition it does not use and keeping `c 13` as the only accepting
  state can only remove accepting paths, so the resulting *path automaton* still
  uniquely accepts `w`.  This is the reduction of Lemma `lem:walk` of the source;
  `UniqueCol c` below is unique acceptance for the path automaton of a colouring `c`.
* `Dset c t v` is the set of states `v` reachable at time `t` by a path/word pair that
  has already *deviated* from the pair `(w, c)` — either by reading a wrong letter or by
  visiting a wrong state.  Unique acceptance fails as soon as `c t ∈ Dset c t` for some
  `t ≤ 13` (`not_uniqueCol_of_Dset`, complete the deviating path along the colouring),
  and conversely it holds when `c 13 ∉ Dset c 13` (`uniqueCol_of_not_Dset`).
* `Dcomp` computes these sets from a finite transition table; it is sound
  (`Dcomp_sound`) for any under-approximation of the transitions and complete
  (`Dcomp_complete`) for the full transition table.
* `dfsU` is a depth-first search over colourings by `6` states which prunes a branch as
  soon as the criterion above fires.  `dfsU_sound` turns a successful search into "no
  `6`-colouring works", and `searchU_ok` runs the search (a machine computation, as in
  Section 7, `sec:verification`, of the source).  Relabelling states
  (`uniqueCol_relabel`) lets the search fix the start state, cutting it by a factor `6`.
* The matching upper bound is the path automaton of the explicit `7`-colouring `c7`.
-/

namespace AneVsAn
namespace Bin

set_option autoImplicit false

/-! ## Unique acceptance for path automata -/

section Colouring

variable {S : Type}

/-- `UniqueCol c` : the path automaton of the colouring `c` (start state `c 0`, unique
accepting state `c 13`) *uniquely accepts* `w` in the sense of Definition 1.1
(`def:complexities`): the only accepting computation of length `13` is the colouring
itself, reading `w`. -/
def UniqueCol (c : ℕ → S) : Prop :=
  ∀ (x : ℕ → Bool) (p : ℕ → S), p 0 = c 0 → p 13 = c 13 →
    (∀ j < 13, Edge c (p j) (x j) (p (j + 1))) →
      (∀ j < 13, x j = wbit j) ∧ (∀ j ≤ 13, p j = c j)

/-- `Dset c t v` : the state `v` is reachable at time `t` in the path automaton of `c`
by a path starting at `c 0` that has already *deviated* from the accepting computation
`(w, c)`, i.e. it has visited a state different from the one prescribed by `c`, or it
has read a letter different from the corresponding letter of `w`. -/
def Dset (c : ℕ → S) (t : ℕ) (v : S) : Prop :=
  ∃ (x : ℕ → Bool) (p : ℕ → S), p 0 = c 0 ∧ p t = v ∧
    (∀ j < t, Edge c (p j) (x j) (p (j + 1))) ∧
      ((∃ j ≤ t, p j ≠ c j) ∨ (∃ j < t, x j ≠ wbit j))

/-- The colouring itself is a path of the path automaton: consecutive positions are
joined by an edge labelled by the corresponding letter of `w`. -/
theorem colour_edges {c : ℕ → S} {j : ℕ} (hj : j < 13) : Edge c (c j) (wbit j) (c (j + 1)) :=
  ⟨j, hj, rfl, rfl, rfl⟩

/-- A deviating path can be prolonged by any edge. -/
theorem Dset_step {c : ℕ → S} {t : ℕ} {u v : S} {a : Bool} (hu : Dset c t u)
    (he : Edge c u a v) : Dset c (t + 1) v := by
  obtain ⟨x, p, hp0, hpt, hp, hdev⟩ := hu
  refine ⟨xext x t a, pext p t v, ?_, pext_succ, edges_pext hp (by rw [hpt]; exact he), ?_⟩
  · rw [pext_le (Nat.zero_le t)]; exact hp0
  · rcases hdev with ⟨j, hj, hne⟩ | ⟨j, hj, hne⟩
    · exact Or.inl ⟨j, by omega, by rwa [pext_le hj]⟩
    · exact Or.inr ⟨j, by omega, by rwa [xext_lt hj]⟩

/-- Reading a *wrong letter* at time `t` from the state `c t` of the colouring produces
a deviating path. -/
theorem Dset_new_letter {c : ℕ → S} {t : ℕ} {v : S} {a : Bool} (ht : t ≤ 13)
    (he : Edge c (c t) a v) (ha : a ≠ wbit t) : Dset c (t + 1) v := by
  refine ⟨xext wbit t a, pext c t v, ?_, pext_succ, ?_, Or.inr ⟨t, by omega, ?_⟩⟩
  · rw [pext_le (Nat.zero_le t)]
  · exact edges_pext (c := c) (t := t) (x := wbit) (p := c) (a := a) (v := v)
      (fun j hj => colour_edges (by omega)) he
  · rwa [xext_self]

/-- Moving to a *wrong state* at time `t + 1` along the correct letter produces a
deviating path. -/
theorem Dset_new_state {c : ℕ → S} {t : ℕ} {v : S} (ht : t ≤ 13)
    (he : Edge c (c t) (wbit t) v) (hv : v ≠ c (t + 1)) : Dset c (t + 1) v := by
  refine ⟨wbit, pext c t v, ?_, pext_succ, ?_, Or.inl ⟨t + 1, le_rfl, ?_⟩⟩
  · rw [pext_le (Nat.zero_le t)]
  · have hex := edges_pext (c := c) (t := t) (x := wbit) (p := c) (a := wbit t) (v := v)
      (fun j hj => colour_edges (by omega)) he
    intro j hj
    have h := hex j hj
    have hx : xext wbit t (wbit t) j = wbit j := by
      by_cases hjt : j < t
      · rw [xext_lt hjt]
      · have : j = t := by omega
        subst this; rw [xext_self]
    rwa [hx] at h
  · rwa [pext_succ]

/-- **The pruning criterion.**  If the state `c t` of the colouring at a time `t ≤ 13`
is also reachable by a deviating path, then the path automaton of `c` has a second
accepting computation of length `13`: follow the deviating path up to time `t` and the
colouring afterwards.  Hence unique acceptance fails. -/
theorem not_uniqueCol_of_Dset {c : ℕ → S} {t : ℕ} (ht : t ≤ 13) (h : Dset c t (c t)) :
    ¬ UniqueCol c := by
  obtain ⟨x, p, hp0, hpt, hp, hdev⟩ := h
  intro huniq
  set P : ℕ → S := fun i => if i ≤ t then p i else c i with hP
  set X : ℕ → Bool := fun i => if i < t then x i else wbit i with hX
  have hPlt : ∀ j, j ≤ t → P j = p j := fun j hj => by simp only [hP, if_pos hj]
  have hPt : ∀ j, t ≤ j → P j = c j := by
    intro j hj
    by_cases hjt : j ≤ t
    · have hje : j = t := by omega
      subst hje
      simp only [hP, if_pos le_rfl]
      exact hpt
    · simp only [hP, if_neg hjt]
  have hP0 : P 0 = c 0 := by rw [hPlt 0 (Nat.zero_le t)]; exact hp0
  have hP13 : P 13 = c 13 := hPt 13 ht
  have hedges : ∀ j < 13, Edge c (P j) (X j) (P (j + 1)) := by
    intro j hj
    by_cases hjt : j < t
    · rw [hPlt j hjt.le, hPlt (j + 1) (by omega)]
      have hXj : X j = x j := by simp only [hX, if_pos hjt]
      rw [hXj]
      exact hp j hjt
    · have hXj : X j = wbit j := by simp only [hX, if_neg hjt]
      rw [hPt j (by omega), hPt (j + 1) (by omega), hXj]
      exact colour_edges hj
  obtain ⟨hxeq, hpeq⟩ := huniq X P hP0 hP13 hedges
  rcases hdev with ⟨j0, hj0, hne⟩ | ⟨j0, hj0, hne⟩
  · refine hne ?_
    rw [← hPlt j0 hj0]
    exact hpeq j0 (by omega)
  · refine hne ?_
    have hXj : X j0 = x j0 := by simp only [hX, if_pos hj0]
    rw [← hXj]
    exact hxeq j0 (by omega)

/-- Conversely, if the accepting state `c 13` is not reachable at time `13` by a
deviating path, then the path automaton of `c` uniquely accepts `w`. -/
theorem uniqueCol_of_not_Dset {c : ℕ → S} (h : ¬ Dset c 13 (c 13)) : UniqueCol c := by
  intro x p hp0 hp13 hedges
  constructor
  · intro j hj
    by_contra hne
    exact h ⟨x, p, hp0, hp13, hedges, Or.inr ⟨j, hj, hne⟩⟩
  · intro j hj
    by_contra hne
    exact h ⟨x, p, hp0, hp13, hedges, Or.inl ⟨j, hj, hne⟩⟩

/-- Relabelling the states by a bijection does not change unique acceptance: the path
automaton of `σ ∘ c` is the path automaton of `c` with its states renamed. -/
theorem uniqueCol_relabel {T : Type} (sig : S ≃ T) {c : ℕ → S} (h : UniqueCol c) :
    UniqueCol (fun i => sig (c i)) := by
  intro x p hp0 hp13 hedges
  set q : ℕ → S := fun i => sig.symm (p i) with hq
  have hq0 : q 0 = c 0 := by simp only [hq, hp0, Equiv.symm_apply_apply]
  have hq13 : q 13 = c 13 := by simp only [hq, hp13, Equiv.symm_apply_apply]
  have hqe : ∀ j < 13, Edge c (q j) (x j) (q (j + 1)) := by
    intro j hj
    obtain ⟨i, hi, h1, h2, h3⟩ := hedges j hj
    exact ⟨i, hi, by simp only [hq, ← h1, Equiv.symm_apply_apply], h2,
      by simp only [hq, ← h3, Equiv.symm_apply_apply]⟩
  obtain ⟨hx, hpq⟩ := h x q hq0 hq13 hqe
  refine ⟨hx, fun j hj => ?_⟩
  have hj' : q j = c j := hpq j hj
  have : sig (q j) = sig (c j) := by rw [hj']
  simpa only [hq, Equiv.apply_symm_apply] using this

end Colouring

/-! ## Computing the deviation sets -/

section Compute

variable {S : Type} [DecidableEq S]

/-- One step of the deviation set: prolong every deviating path by an arbitrary edge,
and add the newly deviating paths — those leaving the state `c t = u` by a wrong letter,
and those leaving it by the correct letter but landing outside `c (t+1) = v`. -/
def dstep (E : EdgeFn S) (D : Finset S) (u : S) (a : Bool) (v : S) : Finset S :=
  ((D.biUnion fun y => E y false ∪ E y true) ∪ E u (!a)) ∪ (E u a).erase v

/-- `Dcomp E c t` computes, using only the transitions listed in `E`, the set of states
reachable at time `t` by a path that has already deviated from `(w, c)`. -/
def Dcomp (E : EdgeFn S) (c : ℕ → S) : ℕ → Finset S
  | 0 => ∅
  | t + 1 => dstep E (Dcomp E c t) (c t) (wbit t) (c (t + 1))

/-- `Dcomp E c t` only depends on the values `c 0, …, c t` of the colouring. -/
theorem Dcomp_congr (E : EdgeFn S) (c c' : ℕ → S) :
    ∀ t : ℕ, (∀ i ≤ t, c i = c' i) → Dcomp E c t = Dcomp E c' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro h
      rw [Dcomp, Dcomp, ih (fun i hi => h i (by omega)), h t (by omega), h (t + 1) le_rfl]

/-- Soundness of the computed deviation sets: if every transition listed in `E` is a
genuine transition of the path automaton of `c`, then `Dcomp E c t ⊆ Dset c t`. -/
theorem Dcomp_sound (c : ℕ → S) (E : EdgeFn S) (hE : ∀ x a y, y ∈ E x a → Edge c x a y) :
    ∀ t : ℕ, t ≤ 13 → ∀ v ∈ Dcomp E c t, Dset c t v := by
  intro t
  induction t with
  | zero => intro _ v hv; simp [Dcomp] at hv
  | succ t ih =>
      intro ht v hv
      rw [Dcomp, dstep] at hv
      rcases Finset.mem_union.1 hv with hv | hv
      · rcases Finset.mem_union.1 hv with hv | hv
        · obtain ⟨u, hu, hv⟩ := Finset.mem_biUnion.1 hv
          rcases Finset.mem_union.1 hv with hv | hv
          · exact Dset_step (ih (by omega) u hu) (hE _ _ _ hv)
          · exact Dset_step (ih (by omega) u hu) (hE _ _ _ hv)
        · exact Dset_new_letter (by omega) (hE _ _ _ hv) (by simp)
      · obtain ⟨hne, hv⟩ := Finset.mem_erase.1 hv
        exact Dset_new_state (by omega) (hE _ _ _ hv) hne

/-- Completeness of the computed deviation sets: if `E` lists every transition of the
path automaton of `c`, then `Dset c t ⊆ Dcomp E c t`. -/
theorem Dcomp_complete (c : ℕ → S) (E : EdgeFn S) (hE : ∀ x a y, Edge c x a y → y ∈ E x a) :
    ∀ t : ℕ, ∀ v, Dset c t v → v ∈ Dcomp E c t := by
  intro t
  induction t with
  | zero =>
      rintro v ⟨x, p, hp0, hpt, -, hdev⟩
      rcases hdev with ⟨j, hj, hne⟩ | ⟨j, hj, -⟩
      · exact absurd (by rw [show j = 0 by omega]; exact hp0) hne
      · omega
  | succ t ih =>
      rintro v ⟨x, p, hp0, hpt, hp, hdev⟩
      rw [Dcomp, dstep]
      by_cases hearly : (∃ j ≤ t, p j ≠ c j) ∨ (∃ j < t, x j ≠ wbit j)
      · -- the deviation has already happened before time `t + 1`
        have hDt : p t ∈ Dcomp E c t :=
          ih _ ⟨x, p, hp0, rfl, fun j hj => hp j (by omega), hearly⟩
        have he : p (t + 1) ∈ E (p t) (x t) := hE _ _ _ (hp t (by omega))
        rw [hpt] at he
        refine Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨p t, hDt, ?_⟩))
        cases hx : x t with
        | false => rw [hx] at he; exact Finset.mem_union_left _ he
        | true => rw [hx] at he; exact Finset.mem_union_right _ he
      · -- the deviation happens exactly at the last step
        push_neg at hearly
        obtain ⟨hstates, hletters⟩ := hearly
        have hpt' : p t = c t := hstates t le_rfl
        have he : p (t + 1) ∈ E (p t) (x t) := hE _ _ _ (hp t (by omega))
        rw [hpt, hpt'] at he
        by_cases hxt : x t = wbit t
        · -- the letters all agree, so the last state must be wrong
          have hlast : v ≠ c (t + 1) := by
            rcases hdev with ⟨j, hj, hne⟩ | ⟨j, hj, hne⟩
            · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hj' | hj'
              · exact absurd (hstates j (by omega)) hne
              · subst hj'
                rw [← hpt]
                exact hne
            · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
              · exact absurd (hletters j hj') hne
              · subst hj'
                exact absurd hxt hne
          refine Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hlast, ?_⟩)
          rw [← hxt]
          exact he
        · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          have : x t = !wbit t := by revert hxt; cases wbit t <;> cases x t <;> simp
          rw [← this]
          exact he

end Compute

/-! ## The lower bound: no `6`-state NFA uniquely accepts `w` -/

/-- The state set used for the lower bound: a hypothetical NFA with at most `6` states. -/
abbrev St6 := Fin 6

/-- Adding one transition `u --a--> v` to a finite transition table. -/
def addEdge6 {S : Type} [DecidableEq S] (E : EdgeFn S) (u : S) (a : Bool) (v : S) : EdgeFn S :=
  fun x b => if x = u ∧ b = a then insert v (E x b) else E x b

/-- The depth-first search over colourings by `6` states.  `dfsU f t c E` returns `true`
if no colouring agreeing with `c` on `0, …, t` and whose transition table contains `E`
can have a uniquely accepting path automaton; `f = 13 - t` is the number of positions
still to be chosen.  A branch is cut as soon as `c t` lies in the computed deviation
set. -/
def dfsU : ℕ → ℕ → (ℕ → St6) → EdgeFn St6 → Bool
  | 0, t, c, E => decide (c t ∈ Dcomp E c t)
  | f + 1, t, c, E =>
      if c t ∈ Dcomp E c t then true
      else decide (∀ v : St6, dfsU f (t + 1) (pext c t v) (addEdge6 E (c t) (wbit t) v) = true)

/-- **Soundness of the search.**  If `dfsU (13 - t) t c' E` succeeds for a partial
colouring `c'` agreeing with `c` up to time `t` and a transition table `E` consisting of
genuine transitions of the path automaton of `c`, then the path automaton of `c` does
not uniquely accept `w`. -/
theorem dfsU_sound (c : ℕ → St6) :
    ∀ f t : ℕ, t + f = 13 → ∀ c' : ℕ → St6, (∀ i ≤ t, c' i = c i) →
      ∀ E : EdgeFn St6, (∀ x a y, y ∈ E x a → Edge c x a y) →
        dfsU f t c' E = true → ¬ UniqueCol c := by
  intro f
  induction f with
  | zero =>
      intro t ht c' hc' E hE hdfs
      have hmem : c' t ∈ Dcomp E c' t := of_decide_eq_true hdfs
      rw [Dcomp_congr E c' c t (fun i hi => hc' i hi), hc' t le_rfl] at hmem
      exact not_uniqueCol_of_Dset (by omega) (Dcomp_sound c E hE t (by omega) _ hmem)
  | succ f ih =>
      intro t ht c' hc' E hE hdfs
      by_cases hmem : c' t ∈ Dcomp E c' t
      · rw [Dcomp_congr E c' c t (fun i hi => hc' i hi), hc' t le_rfl] at hmem
        exact not_uniqueCol_of_Dset (by omega) (Dcomp_sound c E hE t (by omega) _ hmem)
      · rw [dfsU, if_neg hmem] at hdfs
        have hall := of_decide_eq_true hdfs
        have hct : c' t = c t := hc' t le_rfl
        have hnext : ∀ i ≤ t + 1, pext c' t (c (t + 1)) i = c i := by
          intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with hi' | hi'
          · rw [pext_le (by omega : i ≤ t)]; exact hc' i (by omega)
          · subst hi'
            simp only [pext, if_neg (by omega : ¬ t + 1 ≤ t)]
        have hnew : ∀ x a y, y ∈ addEdge6 E (c' t) (wbit t) (c (t + 1)) x a → Edge c x a y := by
          intro x a y hy
          by_cases hxa : x = c' t ∧ a = wbit t
          · rw [addEdge6, if_pos hxa] at hy
            rcases Finset.mem_insert.1 hy with h | h
            · refine ⟨t, by omega, ?_, by rw [hxa.2], h.symm⟩
              rw [hxa.1, hct]
            · exact hE _ _ _ h
          · rw [addEdge6, if_neg hxa] at hy
            exact hE _ _ _ hy
        exact ih (t + 1) (by omega) _ hnext _ hnew (hall (c (t + 1)))

/-- The machine computation: the depth-first search over all colourings of the `14`
positions of `w = 1101000000100` by at most `6` states, with start state `0`, succeeds.
(This is a finite search of the kind described in Section 7, `sec:verification`, of
`anevsanseparationv4.tex`, run for this particular word and `6` states.) -/
theorem searchU_ok : dfsU 13 0 (fun _ => (0 : St6)) (fun _ _ => ∅) = true := by
  native_decide

/-- No colouring of the positions `0, …, 13` by `6` states *whose start state is `0`*
has a uniquely accepting path automaton for `w = 1101000000100`. -/
theorem no_six_colouring_zero (c : ℕ → St6) (h0 : c 0 = 0) : ¬ UniqueCol c := by
  refine dfsU_sound c 13 0 rfl (fun _ => (0 : St6)) ?_ (fun _ _ => ∅) (by simp) searchU_ok
  intro i hi
  have : i = 0 := by omega
  subst this
  exact h0.symm

/-- No colouring of the positions `0, …, 13` by `6` states has a uniquely accepting path
automaton for `w = 1101000000100`: relabel the states so that the start state is `0`. -/
theorem no_six_colouring (c : ℕ → St6) : ¬ UniqueCol c := by
  intro h
  refine no_six_colouring_zero (fun i => Equiv.swap (c 0) 0 (c i)) ?_ (uniqueCol_relabel _ h)
  exact Equiv.swap_apply_left _ _

/-- Every NFA that uniquely accepts `w = 1101000000100` (as a word of length `13`) has
at least `7` states.  Restricting such an NFA to the transitions used by its accepting
path, and to `c 13` as its only accepting state, only removes accepting paths, so the
resulting path automaton would still uniquely accept `w` — contradicting
`no_six_colouring`. -/
theorem uniqueSizes_ge_seven {q : ℕ} (hq : q ∈ UniqueSizes 13 wbit) : 7 ≤ q := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨step, st, acc, ⟨⟨p, hp0, hpacc, hprun⟩, huniq⟩⟩ := hq
  have hq6 : q ≤ 6 := by omega
  set emb : Fin q → St6 := fun v => ⟨v.1, lt_of_lt_of_le v.2 hq6⟩ with hemb
  have hembinj : Function.Injective emb := by
    intro a b hab
    have h : (emb a).val = (emb b).val := congrArg Fin.val hab
    simp only [hemb] at h
    exact Fin.ext h
  haveI : Nonempty (Fin q) := ⟨st⟩
  set g : St6 → Fin q := Function.invFun emb with hg
  have hgemb : ∀ v : Fin q, g (emb v) = v := Function.leftInverse_invFun hembinj
  set c : ℕ → St6 := fun i => emb (p i) with hc
  refine no_six_colouring c ?_
  intro x P hP0 hP13 hedges
  -- every state visited by `P` is in the image of the embedding
  have hrange : ∀ j ≤ 13, ∃ m, P j = emb (p m) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · exact ⟨0, by rw [hj0, hP0]⟩
    · obtain ⟨i, -, -, -, h3⟩ := hedges (j - 1) (by omega)
      exact ⟨i + 1, by rw [show j - 1 + 1 = j by omega] at h3; rw [← h3]⟩
  set pq : ℕ → Fin q := fun i => g (P i) with hpq
  have hemb_pq : ∀ j ≤ 13, P j = emb (pq j) := by
    intro j hj
    obtain ⟨m, hm⟩ := hrange j hj
    simp only [hpq, hm, hgemb]
  have hpq0 : pq 0 = st := by simp only [hpq, hP0, hc, hgemb, hp0]
  have hstep : ∀ i < 13, step (pq i) (x i) (pq (i + 1)) := by
    intro i hi
    obtain ⟨m, hm, h1, h2, h3⟩ := hedges i hi
    have e1 : pq i = p m := by simp only [hpq, ← h1, hc, hgemb]
    have e2 : pq (i + 1) = p (m + 1) := by simp only [hpq, ← h3, hc, hgemb]
    rw [e1, e2, ← h2]
    exact hprun m hm
  have hpq13 : pq 13 = p 13 := by simp only [hpq, hP13, hc, hgemb]
  obtain ⟨hxeq, hpeq⟩ :=
    huniq x pq wbit p ⟨hpq0, by rw [hpq13]; exact hpacc, hstep⟩ ⟨hp0, hpacc, hprun⟩
  refine ⟨hxeq, fun j hj => ?_⟩
  rw [hemb_pq j hj, hpeq j hj]

/-! ## The upper bound: an explicit `7`-state NFA -/

/-- The colouring of the `14` positions of `w = 1101000000100` by `7` states found by
machine search; the associated path automaton is a `7`-state NFA uniquely accepting
`w`. -/
def c7list : List (Fin 7) := [0, 1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 5, 6, 0]

/-- The colouring `c7 : ℕ → Fin 7` of the positions `0, …, 13` given by `c7list`. -/
def c7 (i : ℕ) : Fin 7 := c7list.getD i 0

/-- The transitions of the path automaton of `c7`, as a finite set for each state and
letter. -/
def E7 : EdgeFn (Fin 7) := fun u a =>
  ((Finset.range 13).filter (fun i => c7 i = u ∧ wbit i = a)).image (fun i => c7 (i + 1))

theorem E7_complete : ∀ u a v, Edge c7 u a v → v ∈ E7 u a := by
  rintro u a v ⟨i, hi, h1, h2, h3⟩
  simp only [E7, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  exact ⟨i, ⟨hi, h1, h2⟩, h3⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The machine computation for the upper bound: no deviating computation of the path
automaton of `c7` ends in its accepting state `c7 13`. -/
theorem c7_not_mem : c7 13 ∉ Dcomp E7 c7 13 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The path automaton of the `7`-colouring `c7` uniquely accepts `w = 1101000000100`. -/
theorem uniqueCol_c7 : UniqueCol c7 :=
  uniqueCol_of_not_Dset fun h => c7_not_mem (Dcomp_complete c7 E7 E7_complete 13 _ h)

/-- There is a `7`-state NFA uniquely accepting `w = 1101000000100`: the path automaton
of the colouring `c7`. -/
theorem seven_mem_uniqueSizes : (7 : ℕ) ∈ UniqueSizes 13 wbit := by
  refine ⟨fun u a v => Edge c7 u a v, c7 0, fun v => v = c7 13,
    ⟨⟨c7, rfl, rfl, fun t ht => ⟨t, ht, rfl, rfl, rfl⟩⟩, ?_⟩⟩
  rintro x p y q ⟨hp0, hpacc, hprun⟩ ⟨hq0, hqacc, hqrun⟩
  obtain ⟨hx, hp⟩ := uniqueCol_c7 x p hp0 hpacc hprun
  obtain ⟨hy, hq⟩ := uniqueCol_c7 y q hq0 hqacc hqrun
  exact ⟨fun t ht => by rw [hx t ht, hy t ht], fun t ht => by rw [hp t ht, hq t ht]⟩

/-- At least one NFA uniquely accepts `w = 1101000000100`. -/
theorem uniqueSizes_nonempty : (UniqueSizes 13 wbit).Nonempty := ⟨7, seven_mem_uniqueSizes⟩

/-! ## The results -/

/-- **`A_N(1101000000100) ≥ 7`.**  The unique nondeterministic automatic complexity
(Definition 1.1, `def:complexities`, of `anevsanseparationv4.tex`) of the binary word
`1101000000100` of length `13` is at least `7`. -/
theorem AN_ge_seven : 7 ≤ AN 13 wbit :=
  le_AN (fun _ hq => uniqueSizes_ge_seven hq) uniqueSizes_nonempty

/-- **`A_N(1101000000100) ≤ 7`**, witnessed by the path automaton of `c7`. -/
theorem AN_le_seven : AN 13 wbit ≤ 7 := AN_le seven_mem_uniqueSizes

/-- **`A_N(1101000000100) = 7`.** -/
theorem AN_eq_seven : AN 13 wbit = 7 := le_antisymm AN_le_seven AN_ge_seven

/-- **The separation for the word `1101000000100`:**
`A_{Ne}(1101000000100) = 6 < 7 = A_N(1101000000100)`.  This is a concrete instance of
the phenomenon of Theorem 1.2 (`thm:main`) of `anevsanseparationv4.tex`, that the exact
nondeterministic automatic complexity can be strictly smaller than the unique one. -/
theorem ANe_lt_AN : ANe 13 wbit < AN 13 wbit := by
  rw [ANe_eq_six, AN_eq_seven]
  norm_num

end Bin
end AneVsAn
