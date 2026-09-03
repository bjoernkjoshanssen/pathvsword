import RequestProject.Defs

/-!
# A binary example: `A_{Ne}(1101000000100) = 6`

This file computes the exact nondeterministic automatic complexity
(Definition 1.1, `def:complexities`, of `anevsanseparationv4.tex`) of the binary word

`w = 1101000000100`

of length `13`: it is `6`.  The lower bound `A_{Ne}(w) ≥ 6` is the main point; the
matching upper bound is witnessed by an explicit `6`-state NFA.

The complexities `ANe`/`AN` of `RequestProject/Defs.lean` are stated over an arbitrary
alphabet `Λ`; here the alphabet is `Bool`, with `true = 1` and `false = 0`.

## Outline

* Any NFA with `q` states that exactly accepts `w` has an accepting path
  `c 0, …, c 13`.  Discarding every transition not used by that path and keeping only
  `c 13` as accepting state shrinks the language, so the resulting *path automaton*
  still exactly accepts `w`.  This is the reduction of Lemma `lem:walk` of the source
  (there stated for unique acceptance); `ExactCol c` below is exact acceptance for the
  path automaton of a colouring `c`.
* `Gset c t` is the set of states reachable at time `t` in the path automaton by
  reading the prefix `w 0 ⋯ w (t-1)`, and `Uset c t` the set of states reachable at
  time `t` by reading *some other* word of length `t`.  If ever `c t ∈ Uset c t`, then
  following the colouring from time `t` on produces an accepted word of length `13`
  different from `w`, so exactness fails (`not_exactCol_of_Uset`); conversely
  `ExactCol c` holds as soon as `c 13 ∉ Uset c 13`.
* `guIter` computes `Gset`/`Uset` from a finite set of transitions; it is sound
  (`guIter_sound`) for any under-approximation of the transitions and complete
  (`guIter_complete`) for the full transition set.
* `dfs` is a depth-first search over colourings by `5` states which, at each node,
  computes `Gset`/`Uset` from the transitions of the partial colouring known so far and
  prunes the branch as soon as `c t ∈ Uset c t`.  `dfs_sound` shows that a successful
  search rules out every colouring; `search_ok` runs the search (a machine computation,
  as in Section 7, `sec:verification`, of the source).

## The two machine computations

The pruning makes the search small (a few tens of thousands of nodes), but it is still
too large for kernel reduction, so `search_ok` is discharged by `native_decide`; the
small computation `c6_not_mem` behind the upper bound is discharged by `decide`, hence
checked by the kernel.
-/

namespace AneVsAn
namespace Bin

set_option autoImplicit false

/-! ## The word -/

/-- The binary word `w = 1101000000100`, as a list of bits (`true = 1`). -/
def wlist : List Bool :=
  [true, true, false, true, false, false, false, false, false, false, true, false, false]

/-- The binary word `w = 1101000000100` of length `13`, presented as a function
assigning to a position `t < 13` its bit; positions `≥ 13` are irrelevant.
This is a word over the binary alphabet `Bool` in the sense of Definition 1.1
(`def:complexities`) of `anevsanseparationv4.tex`. -/
def wbit (i : ℕ) : Bool := wlist.getD i false

/-! ## Path automata of a colouring

Throughout, a *colouring* is a map `c : ℕ → S` assigning a state to each of the
positions `0, …, 13` of `w`. -/

section Colouring

variable {S : Type}

/-- The transitions of the *path automaton* of a colouring `c` of the positions
`0, …, 13` of `w`: an edge `u --a--> v` exists iff some position `i < 13` has
`c i = u`, `c (i+1) = v` and `w i = a`.  (Compare the walk graph of Lemma `lem:walk`
in `anevsanseparationv4.tex`.) -/
def Edge (c : ℕ → S) (u : S) (a : Bool) (v : S) : Prop :=
  ∃ i, i < 13 ∧ c i = u ∧ wbit i = a ∧ c (i + 1) = v

/-- `Gset c t v` : the state `v` is reachable in the path automaton of `c` from `c 0`
by a path of length `t` spelling the prefix `w 0 ⋯ w (t-1)` of `w`. -/
def Gset (c : ℕ → S) (t : ℕ) (v : S) : Prop :=
  ∃ p : ℕ → S, p 0 = c 0 ∧ p t = v ∧ ∀ j < t, Edge c (p j) (wbit j) (p (j + 1))

/-- `Uset c t v` : the state `v` is reachable in the path automaton of `c` from `c 0`
by a path of length `t` spelling some word *different* from the prefix
`w 0 ⋯ w (t-1)` of `w`. -/
def Uset (c : ℕ → S) (t : ℕ) (v : S) : Prop :=
  ∃ (x : ℕ → Bool) (p : ℕ → S), (∃ j < t, x j ≠ wbit j) ∧ p 0 = c 0 ∧ p t = v ∧
    ∀ j < t, Edge c (p j) (x j) (p (j + 1))

/-- `ExactCol c` : the path automaton of the colouring `c`, with start state `c 0` and
unique accepting state `c 13`, *exactly accepts* `w` in the sense of Definition 1.1
(`def:complexities`): every word of length `13` that it accepts equals `w`. -/
def ExactCol (c : ℕ → S) : Prop :=
  ∀ (x : ℕ → Bool) (p : ℕ → S), p 0 = c 0 → p 13 = c 13 →
    (∀ j < 13, Edge c (p j) (x j) (p (j + 1))) → ∀ j < 13, x j = wbit j

/-! ### Extending paths -/

/-- Extension of a path `p` of length `t` by one step to a state `v`. -/
def pext (p : ℕ → S) (t : ℕ) (v : S) : ℕ → S := fun i => if i ≤ t then p i else v

/-- Extension of a word `x` of length `t` by one letter `a`. -/
def xext (x : ℕ → Bool) (t : ℕ) (a : Bool) : ℕ → Bool := fun i => if i < t then x i else a

theorem pext_le {p : ℕ → S} {t : ℕ} {v : S} {i : ℕ} (h : i ≤ t) : pext p t v i = p i := by
  simp [pext, h]

theorem pext_succ {p : ℕ → S} {t : ℕ} {v : S} : pext p t v (t + 1) = v := by
  simp [pext]

theorem xext_lt {x : ℕ → Bool} {t : ℕ} {a : Bool} {i : ℕ} (h : i < t) : xext x t a i = x i := by
  simp [xext, h]

theorem xext_self {x : ℕ → Bool} {t : ℕ} {a : Bool} : xext x t a t = a := by
  simp [xext]

/-- The extended pair `(xext x t a, pext p t v)` is again a path, one step longer. -/
theorem edges_pext {c : ℕ → S} {t : ℕ} {x : ℕ → Bool} {p : ℕ → S} {a : Bool} {v : S}
    (hp : ∀ j < t, Edge c (p j) (x j) (p (j + 1))) (he : Edge c (p t) a v) :
    ∀ j < t + 1, Edge c (pext p t v j) (xext x t a j) (pext p t v (j + 1)) := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | heq
  · rw [pext_le hlt.le, pext_le (by omega : j + 1 ≤ t), xext_lt hlt]
    exact hp j hlt
  · subst heq
    rw [pext_le le_rfl, pext_succ, xext_self]
    exact he

/-- One step of the reachability set along the correct letter of `w`. -/
theorem Gset_step {c : ℕ → S} {t : ℕ} {u v : S} (hu : Gset c t u)
    (he : Edge c u (wbit t) v) : Gset c (t + 1) v := by
  obtain ⟨p, hp0, hpt, hp⟩ := hu
  refine ⟨pext p t v, ?_, pext_succ, ?_⟩
  · rw [pext_le (Nat.zero_le t)]; exact hp0
  · have hex := edges_pext (x := wbit) hp (by rw [hpt]; exact he)
    intro j hj
    have h := hex j hj
    have hx : xext wbit t (wbit t) j = wbit j := by
      by_cases hjt : j < t
      · rw [xext_lt hjt]
      · have : j = t := by omega
        subst this; rw [xext_self]
    rwa [hx] at h

/-- One step of the "wrong prefix" reachability set, along an arbitrary letter. -/
theorem Uset_step {c : ℕ → S} {t : ℕ} {u v : S} {a : Bool} (hu : Uset c t u)
    (he : Edge c u a v) : Uset c (t + 1) v := by
  obtain ⟨x, p, ⟨j0, hj0, hne⟩, hp0, hpt, hp⟩ := hu
  refine ⟨xext x t a, pext p t v, ⟨j0, by omega, ?_⟩, ?_, pext_succ,
    edges_pext hp (by rw [hpt]; exact he)⟩
  · rwa [xext_lt hj0]
  · rw [pext_le (Nat.zero_le t)]; exact hp0

/-- A correct prefix followed by a wrong letter enters the "wrong prefix"
reachability set. -/
theorem Uset_new {c : ℕ → S} {t : ℕ} {u v : S} {a : Bool} (hu : Gset c t u)
    (he : Edge c u a v) (ha : a ≠ wbit t) : Uset c (t + 1) v := by
  obtain ⟨p, hp0, hpt, hp⟩ := hu
  refine ⟨xext wbit t a, pext p t v, ⟨t, by omega, ?_⟩, ?_, pext_succ, ?_⟩
  · rwa [xext_self]
  · rw [pext_le (Nat.zero_le t)]; exact hp0
  · refine edges_pext (x := wbit) ?_ (by rw [hpt]; exact he)
    intro j hj; exact hp j hj

/-- **The pruning criterion.**  If the state `c t` occupied by the colouring at time
`t ≤ 13` can also be reached at time `t` by reading a word different from the prefix
`w 0 ⋯ w (t-1)`, then the path automaton of `c` accepts a word of length `13`
different from `w`: follow the colouring from time `t` on.  Hence exactness fails. -/
theorem not_exactCol_of_Uset {c : ℕ → S} {t : ℕ} (ht : t ≤ 13) (h : Uset c t (c t)) :
    ¬ ExactCol c := by
  obtain ⟨x, p, ⟨j0, hj0, hne⟩, hp0, hpt, hp⟩ := h
  intro hex
  set P : ℕ → S := fun i => if i ≤ t then p i else c i with hP
  set X : ℕ → Bool := fun i => if i < t then x i else wbit i with hX
  have hPt : ∀ j, t ≤ j → P j = c j := by
    intro j hj
    by_cases hjt : j ≤ t
    · have : j = t := by omega
      subst this
      simp only [hP, if_pos le_rfl]
      exact hpt
    · simp only [hP, if_neg hjt]
  have hPlt : ∀ j, j ≤ t → P j = p j := by
    intro j hj; simp only [hP, if_pos hj]
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
      exact ⟨j, hj, rfl, rfl, rfl⟩
  have hgood := hex X P hP0 hP13 hedges j0 (by omega)
  have hXj0 : X j0 = x j0 := by simp only [hX, if_pos hj0]
  rw [hXj0] at hgood
  exact hne hgood

/-- Conversely, if no word other than `w` reaches `c 13` at time `13`, then the path
automaton of `c` exactly accepts `w`. -/
theorem exactCol_of_not_Uset {c : ℕ → S} (h : ¬ Uset c 13 (c 13)) : ExactCol c := by
  intro x p hp0 hp13 hedges j hj
  by_contra hne
  exact h ⟨x, p, ⟨j, hj, hne⟩, hp0, by rw [hp13], hedges⟩

end Colouring

/-! ## Computing the reachability sets -/

section Compute

variable {S : Type} [DecidableEq S]

/-- A finite description of a set of transitions: for each state and letter, a finite
set of successors. -/
abbrev EdgeFn (S : Type) := S → Bool → Finset S

/-- The subset-construction transition: the set of successors of a set of states. -/
def dlt (E : EdgeFn S) (T : Finset S) (a : Bool) : Finset S := T.biUnion (fun u => E u a)

/-- `guIter E c0 t = (G, U)` computes, using only the transitions in `E`, the set `G`
of states reachable from `c0` at time `t` by the prefix of `w`, and the set `U` of
states reachable at time `t` by a word different from that prefix. -/
def guIter (E : EdgeFn S) (c0 : S) : ℕ → Finset S × Finset S
  | 0 => ({c0}, ∅)
  | t + 1 =>
      (dlt E (guIter E c0 t).1 (wbit t),
        (dlt E (guIter E c0 t).2 false ∪ dlt E (guIter E c0 t).2 true) ∪
          dlt E (guIter E c0 t).1 (!wbit t))

/-- Soundness of the computed reachability sets: if every transition of `E` is a
genuine transition of the path automaton of `c`, then the sets computed by `guIter`
are contained in `Gset c t` and `Uset c t`. -/
theorem guIter_sound (c : ℕ → S) (E : EdgeFn S) (hE : ∀ x a y, y ∈ E x a → Edge c x a y) :
    ∀ t, (∀ v ∈ (guIter E (c 0) t).1, Gset c t v) ∧
      (∀ v ∈ (guIter E (c 0) t).2, Uset c t v) := by
  intro t
  induction t with
  | zero =>
      constructor
      · intro v hv
        simp only [guIter, Finset.mem_singleton] at hv
        exact ⟨fun _ => c 0, rfl, hv.symm, by omega⟩
      · intro v hv
        simp [guIter] at hv
  | succ t ih =>
      obtain ⟨ihG, ihU⟩ := ih
      constructor
      · intro v hv
        simp only [guIter, dlt, Finset.mem_biUnion] at hv
        obtain ⟨u, hu, hv⟩ := hv
        exact Gset_step (ihG u hu) (hE _ _ _ hv)
      · intro v hv
        simp only [guIter, dlt, Finset.mem_union, Finset.mem_biUnion] at hv
        rcases hv with (⟨u, hu, hv⟩ | ⟨u, hu, hv⟩) | ⟨u, hu, hv⟩
        · exact Uset_step (ihU u hu) (hE _ _ _ hv)
        · exact Uset_step (ihU u hu) (hE _ _ _ hv)
        · refine Uset_new (ihG u hu) (hE _ _ _ hv) ?_
          simp

/-- Completeness of the computed reachability sets: if `E` contains every transition of
the path automaton of `c`, then `Gset c t` and `Uset c t` are contained in the sets
computed by `guIter`. -/
theorem guIter_complete (c : ℕ → S) (E : EdgeFn S) (hE : ∀ x a y, Edge c x a y → y ∈ E x a) :
    ∀ t, (∀ v, Gset c t v → v ∈ (guIter E (c 0) t).1) ∧
      (∀ v, Uset c t v → v ∈ (guIter E (c 0) t).2) := by
  intro t
  induction t with
  | zero =>
      constructor
      · rintro v ⟨p, hp0, hpt, -⟩
        simp only [guIter, Finset.mem_singleton]
        rw [← hpt, hp0]
      · rintro v ⟨x, p, ⟨j0, hj0, -⟩, -⟩
        omega
  | succ t ih =>
      obtain ⟨ihG, ihU⟩ := ih
      constructor
      · rintro v ⟨p, hp0, hpt, hp⟩
        have hGt : p t ∈ (guIter E (c 0) t).1 :=
          ihG _ ⟨p, hp0, rfl, fun j hj => hp j (by omega)⟩
        have he : p (t + 1) ∈ E (p t) (wbit t) := hE _ _ _ (hp t (by omega))
        simp only [guIter, dlt, Finset.mem_biUnion]
        exact ⟨p t, hGt, by rw [← hpt]; exact he⟩
      · rintro v ⟨x, p, ⟨j0, hj0, hne⟩, hp0, hpt, hp⟩
        simp only [guIter, dlt, Finset.mem_union, Finset.mem_biUnion]
        by_cases hbad : ∃ j < t, x j ≠ wbit j
        · -- the word already differs from `w` before time `t`
          have hUt : p t ∈ (guIter E (c 0) t).2 :=
            ihU _ ⟨x, p, hbad, hp0, rfl, fun j hj => hp j (by omega)⟩
          have he : p (t + 1) ∈ E (p t) (x t) := hE _ _ _ (hp t (by omega))
          rw [hpt] at he
          cases hx : x t with
          | false => exact Or.inl (Or.inl ⟨p t, hUt, by rw [← hx]; exact he⟩)
          | true => exact Or.inl (Or.inr ⟨p t, hUt, by rw [← hx]; exact he⟩)
        · -- the word agrees with `w` up to time `t`, and differs at time `t`
          push_neg at hbad
          have hj0t : j0 = t := by
            by_contra h
            exact hne (hbad j0 (by omega))
          subst hj0t
          have hGt : p j0 ∈ (guIter E (c 0) j0).1 := by
            refine ihG _ ⟨p, hp0, rfl, fun j hj => ?_⟩
            have := hp j (by omega)
            rwa [hbad j hj] at this
          have he : p (j0 + 1) ∈ E (p j0) (x j0) := hE _ _ _ (hp j0 (by omega))
          have hxt : x j0 = !wbit j0 := by
            revert hne; cases wbit j0 <;> cases x j0 <;> simp
          rw [hpt, hxt] at he
          exact Or.inr ⟨p j0, hGt, he⟩

end Compute

/-! ## The lower bound: no `5`-state NFA -/

/-- The state set used for the lower bound: a hypothetical NFA with at most `5` states. -/
abbrev St := Fin 5

/-- Adding one transition `u --a--> v` to a finite transition set. -/
def addEdge (E : EdgeFn St) (u : St) (a : Bool) (v : St) : EdgeFn St :=
  fun x b => if x = u ∧ b = a then insert v (E x b) else E x b

/-- The depth-first search over colourings.  `dfs f t c0 u E` returns `true` if no
colouring `c` with `c 0 = c0`, `c t = u` and transition set containing `E` can have an
exactly accepting path automaton; `f = 13 - t` is the remaining number of positions.
The branch is cut as soon as `u` lies in the computed "wrong word" reachability set. -/
def dfs : ℕ → ℕ → St → St → EdgeFn St → Bool
  | 0, t, c0, u, E => decide (u ∈ (guIter E c0 t).2)
  | f + 1, t, c0, u, E =>
      if u ∈ (guIter E c0 t).2 then true
      else decide (∀ v : St, dfs f (t + 1) c0 v (addEdge E u (wbit t) v) = true)

/-- **Soundness of the search.**  If `dfs (13 - t) t (c 0) (c t) E` succeeds for a
transition set `E` consisting of genuine transitions of the path automaton of `c`,
then the path automaton of `c` does not exactly accept `w`. -/
theorem dfs_sound (c : ℕ → St) :
    ∀ (f t : ℕ), t + f = 13 → ∀ E : EdgeFn St, (∀ x a y, y ∈ E x a → Edge c x a y) →
      dfs f t (c 0) (c t) E = true → ¬ ExactCol c := by
  intro f
  induction f with
  | zero =>
      intro t ht E hE hdfs
      have hmem : c t ∈ (guIter E (c 0) t).2 := of_decide_eq_true hdfs
      exact not_exactCol_of_Uset (by omega) ((guIter_sound c E hE t).2 _ hmem)
  | succ f ih =>
      intro t ht E hE hdfs
      by_cases hmem : c t ∈ (guIter E (c 0) t).2
      · exact not_exactCol_of_Uset (by omega) ((guIter_sound c E hE t).2 _ hmem)
      · rw [dfs, if_neg hmem] at hdfs
        have hall := of_decide_eq_true hdfs
        have hnew : ∀ x a y, y ∈ addEdge E (c t) (wbit t) (c (t + 1)) x a → Edge c x a y := by
          intro x a y hy
          by_cases hxa : x = c t ∧ a = wbit t
          · rw [addEdge, if_pos hxa] at hy
            rcases Finset.mem_insert.1 hy with h | h
            · exact ⟨t, by omega, hxa.1.symm, by rw [hxa.2], h.symm⟩
            · exact hE _ _ _ h
          · rw [addEdge, if_neg hxa] at hy
            exact hE _ _ _ hy
        exact ih (t + 1) (by omega) _ hnew (hall (c (t + 1)))

/-- The machine computation: the depth-first search over all colourings of the `14`
positions of `w = 1101000000100` by at most `5` states succeeds.  (This is a finite
search of the kind described in Section 7, `sec:verification`, of
`anevsanseparationv4.tex`, run for this particular word and `5` states.) -/
theorem search_ok : ∀ c0 : St, dfs 13 0 c0 c0 (fun _ _ => ∅) = true := by
  native_decide

/-- No colouring of the positions `0, …, 13` by `5` states has an exactly accepting
path automaton for `w = 1101000000100`. -/
theorem no_five_colouring (c : ℕ → St) : ¬ ExactCol c := by
  refine dfs_sound c 13 0 rfl (fun _ _ => ∅) (by simp) ?_
  exact search_ok (c 0)

/-- Every NFA that exactly accepts `w = 1101000000100` (as a word of length `13`) has
at least `6` states.  Restricting such an NFA to the transitions used by an accepting
path, and to `c 13` as its only accepting state, only shrinks its language, so the
resulting path automaton would still exactly accept `w` — contradicting
`no_five_colouring`. -/
theorem exactSizes_ge_six {q : ℕ} (hq : q ∈ ExactSizes 13 wbit) : 6 ≤ q := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨step, st, acc, ⟨⟨p, hp0, hpacc, hprun⟩, hexact⟩⟩ := hq
  have hq5 : q ≤ 5 := by omega
  -- embed the states into `Fin 5`
  set emb : Fin q → St := fun v => ⟨v.1, lt_of_lt_of_le v.2 hq5⟩ with hemb
  have hembinj : Function.Injective emb := by
    intro a b hab
    have h : (emb a).val = (emb b).val := congrArg Fin.val hab
    simp only [hemb] at h
    exact Fin.ext h
  haveI : Nonempty (Fin q) := ⟨st⟩
  set g : St → Fin q := Function.invFun emb with hg
  have hgemb : ∀ v : Fin q, g (emb v) = v := Function.leftInverse_invFun hembinj
  set c : ℕ → St := fun i => emb (p i) with hc
  refine no_five_colouring c ?_
  intro x P hP0 hP13 hedges j hj
  -- pull the path back to the original state set
  set pq : ℕ → Fin q := fun i => g (P i) with hpq
  have hpq0 : pq 0 = st := by
    simp only [hpq, hP0, hc, hgemb, hp0]
  have hstep : ∀ i < 13, step (pq i) (x i) (pq (i + 1)) := by
    intro i hi
    obtain ⟨m, hm, h1, h2, h3⟩ := hedges i hi
    have e1 : pq i = p m := by simp only [hpq, ← h1, hc, hgemb]
    have e2 : pq (i + 1) = p (m + 1) := by simp only [hpq, ← h3, hc, hgemb]
    rw [e1, e2, ← h2]
    exact hprun m hm
  have hpq13 : pq 13 = p 13 := by simp only [hpq, hP13, hc, hgemb]
  exact hexact x pq ⟨hpq0, by rw [hpq13]; exact hpacc, hstep⟩ j hj

/-! ## The upper bound: an explicit `6`-state NFA -/

/-- The colouring of the `14` positions of `w = 1101000000100` by `6` states found by
machine search; the associated path automaton is a `6`-state NFA exactly accepting
`w`. -/
def clist : List (Fin 6) := [0, 1, 2, 3, 4, 5, 4, 5, 5, 4, 1, 2, 3, 0]

/-- The colouring `c6 : ℕ → Fin 6` of the positions `0, …, 13` given by `clist`. -/
def c6 (i : ℕ) : Fin 6 := clist.getD i 0

/-- The transitions of the path automaton of `c6`, as a finite set for each state and
letter. -/
def E6 : EdgeFn (Fin 6) := fun u a =>
  ((Finset.range 13).filter (fun i => c6 i = u ∧ wbit i = a)).image (fun i => c6 (i + 1))

theorem E6_complete : ∀ u a v, Edge c6 u a v → v ∈ E6 u a := by
  rintro u a v ⟨i, hi, h1, h2, h3⟩
  simp only [E6, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  exact ⟨i, ⟨hi, h1, h2⟩, h3⟩

set_option maxRecDepth 100000 in
/-- The machine computation for the upper bound: reading any word other than `w` leaves
the path automaton of `c6` outside its accepting state `c6 13`. -/
theorem c6_not_mem : c6 13 ∉ (guIter E6 (c6 0) 13).2 := by
  decide

/-- The path automaton of the `6`-colouring `c6` exactly accepts `w = 1101000000100`. -/
theorem exactCol_c6 : ExactCol c6 :=
  exactCol_of_not_Uset fun h => c6_not_mem ((guIter_complete c6 E6 E6_complete 13).2 _ h)

/-- There is a `6`-state NFA exactly accepting `w = 1101000000100`: the path automaton
of the colouring `c6`. -/
theorem six_mem_exactSizes : (6 : ℕ) ∈ ExactSizes 13 wbit := by
  refine ⟨fun u a v => Edge c6 u a v, c6 0, fun v => v = c6 13,
    ⟨⟨c6, rfl, rfl, fun t ht => ⟨t, ht, rfl, rfl, rfl⟩⟩, ?_⟩⟩
  rintro x p ⟨hp0, hpacc, hrun⟩ t ht
  exact exactCol_c6 x p hp0 hpacc hrun t ht

/-- At least one NFA exactly accepts `w = 1101000000100`. -/
theorem exactSizes_nonempty : (ExactSizes 13 wbit).Nonempty := ⟨6, six_mem_exactSizes⟩

/-! ## The result -/

/-- **`A_{Ne}(1101000000100) ≥ 6`.**  The exact nondeterministic automatic complexity
(Definition 1.1, `def:complexities`, of `anevsanseparationv4.tex`) of the binary word
`1101000000100` of length `13` is at least `6`. -/
theorem ANe_ge_six : 6 ≤ ANe 13 wbit :=
  le_ANe (fun _ hq => exactSizes_ge_six hq) exactSizes_nonempty

/-- **`A_{Ne}(1101000000100) ≤ 6`**, witnessed by the path automaton of `c6`. -/
theorem ANe_le_six : ANe 13 wbit ≤ 6 := ANe_le six_mem_exactSizes

/-- **`A_{Ne}(1101000000100) = 6`.** -/
theorem ANe_eq_six : ANe 13 wbit = 6 := le_antisymm ANe_le_six ANe_ge_six

end Bin
end AneVsAn
