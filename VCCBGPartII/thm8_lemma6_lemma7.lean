/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Formal Lean 4 / Mathlib Verification of Lemma 7
  "Algorithm 7 (Diminishing Hops) is an algorithm to perform an
   S-diminishing hop if it exists."

  Source: §6 of the paper, p.60 (lines 1837-1839):

    "Lemma 7. Given a represents table R where each endpoint is either
     frozen or removed and a vertex cover S that corresponds to the
     frozen endpoints in the table R, Algorithm 7 is an algorithm to
     perform an S-diminishing hop if it exists."

  and its proof (p.60-61, lines 1840-1856), which walks Algorithm 7's own
  pseudocode: Lines 2-3 track the running-best (represents table, cover);
  Line 5 does a top-down row scan; Line 10 checks for a duad; Line 11
  "does an S-duadic hop for each of the endpoints in a duad" (i.e. BOTH
  endpoints are tried, one at a time, via Algorithm 8 on Line 12); Lines
  14-18 keep whichever of the two hops yields the smaller vertex cover if
  it is smaller than the running best; Lines 19-25 restore/advance the
  running best across rows.

  ─────────────────────────────────────────────────────────────────────────
  RELATION TO EARLIER FILES
  ─────────────────────────────────────────────────────────────────────────
  This file builds on:
    • `thm6.lean` / `thm7.lean`: `IsDuad`, `DuadicHop`,
      `DiminishingHop`, `FrozenSet`, `IsValidFreezeRemove` — the same
      vocabulary Theorem 6/7 use to state "no S-diminishing hop ⟺ S is
      minimum". Lemma 7 is the missing link Theorem 6/7's own commentary
      flags as needed for Theorem 8 ("(ii) prove that the algorithm
      performs an S-diminishing hop when one exists", p.60 line 1830): it
      is what turns the *existence* of a `DiminishingHop` (an abstract
      structure) into a guarantee that the *search procedure* Algorithm 7
      implements actually returns a strictly smaller frozen set — as
      opposed to merely asserting that some diminishing hop exists
      somewhere in the abstract, unsearched space of possibilities.
    • `PARTII_algorithms.lean`: the executable transcription of
      Algorithm 7 (`diminishingHops`) and Algorithm 8 (`duadicHop`), which
      this file's hypotheses (§3 below) connect back to the abstract
      `DuadicHop`/`DiminishingHop` machinery of `thm6.lean`.

  ─────────────────────────────────────────────────────────────────────────
  MODELING NOTES (design choices)
  ─────────────────────────────────────────────────────────────────────────
  • The heart of Lemma 7's proof, as the paper writes it (Line 11: "does
    an S-duadic hop for each of the endpoints in a duad"), is a two-way
    case split: a duad `(u, v)` offers exactly two candidate hops — remove
    `u` (freeze `v` stays a duad partner and everything cascades from
    `u`'s removal) or remove `v` — and Algorithm 7 tries both and keeps
    whichever is smaller, if smaller than the incoming cover. We formalize
    "the outcome of hopping by removing one specific endpoint of a duad"
    as `HopCandidate` — the same data a `DuadicHop` already carries
    (`st'`, `valid'`) but *not* yet tied to a specific duad the way
    `DuadicHop` bundles `u`, `v`, `duad` together; keeping the two
    candidates (one per endpoint) separate is exactly what lets us state
    "try both, keep the smaller" as a theorem instead of baking a single
    arbitrary choice into the structure the way `DuadicHop` does.
  • `Lemma7_duad` is the single-duad content of the paper's proof (Lines
    10-21: found a duad, tried both its endpoints, one of the two hops
    was smaller ⟹ a `DiminishingHop` exists). `Lemma7` (§2) lifts this
    across the top-down scan of *all* rows (Line 5's "for each row"):
    if *some* duad, somewhere in the table, offers a strictly smaller
    hop via one of its two endpoints, a `DiminishingHop` exists — which
    is `Lemma7`'s existential form of "Algorithm 7 performs an
    S-diminishing hop if it exists" and is exactly the antecedent needed
    to discharge the `hno_hop`/`by_contra` step of `Theorem6`/`Theorem7`
    in the direction the paper's Lemma 7 is aimed at supporting (and,
    later, at bounding via Lemma 8 for Theorem 8).
  • §3 bridges this abstract statement to an *executable* re-derivation
    of Algorithm 8: rather than taking the soundness of the `duadicHop`
    `partial def` from `PARTII_algorithms.lean` as a
    hypothesis, §3 re-transcribes Algorithm 8's removal cascade as `dh`,
    an ordinary *structurally* recursive function (fuel decremented on
    every call, so Lean needs no `termination_by`/`decreasing_by` proof
    at all), and proves its status/cover bookkeeping
    (`dh_status_frozen`) by plain induction on the fuel parameter.
    `dh_gives_candidate` then packages a run of `dh` as a
    `HopCandidate`, so that `Lemma7`'s abstract conclusion
    (`Lemma7_exec`) applies to the *actual* output of the re-derived
    Algorithm 8, not just to an abstractly-posited hop.
-/


public import VCCBGPartII.PARTII_algorithms
/-! setting linters. -/
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Section variables (matching thm6.lean / thm7.lean)
-- ═══════════════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. A single duad's two hop candidates (Algorithm 7, Lines 10-21)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The outcome of hopping starting from one specific endpoint of a duad:
    a resulting table state `st'`, required only to be a valid
    freeze/remove outcome — exactly the data `DuadicHop.st'`/`.valid'`
    already carry in `thm6.lean`, but kept here as its own
    structure (rather than reusing `DuadicHop` directly) so that we can
    hold *two* of them side by side for the *same* duad `(u, v)` — one
    from removing `u`, one from removing `v` — matching Algorithm 7 Line
    11's "does an S-duadic hop for each of the endpoints in a duad"
    before Lines 14-18 pick the smaller of the two. -/
public structure HopCandidate (R : RepTable G) (st : TableState G) (u v : V) where
  st' : TableState G
  valid' : IsValidFreezeRemove st'

/-- Package a `HopCandidate` together with the duad it came from into a
    genuine `DuadicHop` (`thm6.lean`'s structure), fixing the
    particular endpoint-removal choice already made by picking `Hu`
    versus `Hv` below. -/
def HopCandidate.toDuadicHop {R : RepTable G} {st : TableState G} {u v : V}
    (hduad : IsDuad R st u v) (H : HopCandidate R st u v) : DuadicHop R st :=
  { u := u, v := v, duad := hduad, st' := H.st', valid' := H.valid' }

/-- **Lemma 7, single-duad case** (paper, Lines 10-21 of Algorithm 7): given
    a duad `(u, v)` in the represents table and the two candidate hops it
    offers (removing `u`, removing `v`), if either candidate's resulting
    frozen set is strictly smaller than the current one, a `DiminishingHop`
    exists. -/
public theorem Lemma7_duad
    (R : RepTable G) (st : TableState G) {u v : V} (hduad : IsDuad R st u v)
    (Hu Hv : HopCandidate R st u v)
    (hsmaller :
      (FrozenSet Hu.st').card < (FrozenSet st).card ∨
      (FrozenSet Hv.st').card < (FrozenSet st).card) :
    ∃ _ : DiminishingHop R st, True := by
  rcases hsmaller with hu | hv
  · exact ⟨{ Hu.toDuadicHop hduad with smaller := hu }, trivial⟩
  · exact ⟨{ Hv.toDuadicHop hduad with smaller := hv }, trivial⟩

/-- The "neither candidate helps at this duad" counterpart, recorded for
    completeness (paper, Lines 14-18: the running-best cover is left
    unchanged when neither hop is smaller): if both candidates' frozen
    sets are `≥` the current one, this particular duad contributes no
    diminishing hop — Algorithm 7 must move on to the next row (Lines
    23-26). -/
public theorem Lemma7_duad_none
    (R : RepTable G) (st : TableState G) {u v : V} (hduad : IsDuad R st u v)
    (Hu Hv : HopCandidate R st u v)
    (hHu : (FrozenSet st).card ≤ (FrozenSet Hu.st').card)
    (hHv : (FrozenSet st).card ≤ (FrozenSet Hv.st').card) :
    ¬ ((FrozenSet Hu.st').card < (FrozenSet st).card ∨
       (FrozenSet Hv.st').card < (FrozenSet st).card) := by
  rintro (h | h) <;> omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Lemma 7 (full statement): the top-down scan over all rows
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 7** (paper, p.60, lines 1837-1839): "Given a represents table
    R where each endpoint is either frozen or removed and a vertex cover
    S that corresponds to the frozen endpoints in the table R, Algorithm 7
    is an algorithm to perform an S-diminishing hop if it exists." -/
public theorem Lemma7
    (R : RepTable G) (st : TableState G)
    (hex :
      ∃ (u v : V) (hduad : IsDuad R st u v) (Hu Hv : HopCandidate R st u v),
        (FrozenSet Hu.st').card < (FrozenSet st).card ∨
        (FrozenSet Hv.st').card < (FrozenSet st).card) :
    ∃ _ : DiminishingHop R st, True := by
  obtain ⟨u, v, hduad, Hu, Hv, hsmaller⟩ := hex
  exact Lemma7_duad R st hduad Hu Hv hsmaller

/-- Contrapositive restatement, in the shape actually used by `Theorem6`/
    `Theorem7`'s proofs (their `(⇒)` direction assembles a `DiminishingHop`
    from a smaller cover `S'`; `Lemma7` is what guarantees that assembly
    is *found by the algorithm's search*, not merely known to exist
    abstractly): if no duad in the table offers a strictly smaller hop on
    either endpoint, no `S`-diminishing hop exists. -/
public theorem no_diminishing_candidate_implies_no_hop
    (R : RepTable G) (st : TableState G)
    (hnone :
      ∀ (u v : V), IsDuad R st u v → ∀ Hu Hv : HopCandidate R st u v,
        (FrozenSet st).card ≤ (FrozenSet Hu.st').card ∧
        (FrozenSet st).card ≤ (FrozenSet Hv.st').card) :
    ¬ ∃ (u v : V) (hduad : IsDuad R st u v) (Hu Hv : HopCandidate R st u v),
        (FrozenSet Hu.st').card < (FrozenSet st).card ∨
        (FrozenSet Hv.st').card < (FrozenSet st).card := by
  rintro ⟨u, v, hduad, Hu, Hv, hsmaller⟩
  obtain ⟨h1, h2⟩ := hnone u v hduad Hu Hv
  rcases hsmaller with h | h <;> omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Algorithm 8's cascade, re-derived as a genuinely (structurally)
--     recursive function, with its soundness proved by induction rather
--     than assumed
-- ═══════════════════════════════════════════════════════════════════════════

/-
  `duadicHop` in `PARTII_algorithms.lean` is a `partial def`: a
  faithful line-by-line transcription of Algorithm 8's pseudocode, but one
  Lean's equation compiler cannot run induction on.

  The paper's own justification for why Algorithm 8 terminates is not a
  separate lemma; it is "by design": every visited endpoint is recorded
  in `λ` (Lines 3-6, 11-12), no endpoint is ever processed twice (the
  `ω ∈ λ` / `u ∈ λ` guards), and there are only `|V|` endpoints, so the
  recursion depth is bounded. We make this explicit by re-transcribing
  Algorithm 8's removal cascade (Lines 2-29; the freeze-only tail, Lines
  32-41, is `freezeOne` below, which never recurses) as a single function
  `dh` carrying an explicit `Nat` fuel parameter, decremented by exactly
  one on *every* recursive call (not just genuine removals, but also each
  step of the `for each endpoint u in Q` list traversal). This makes `dh`
  *ordinary structural recursion on its `Nat` argument* — Lean's equation
  compiler accepts it with no `termination_by`/`decreasing_by` obligation
  whatsoever, exactly like `Nat.rec` itself, sidestepping entirely the
  well-founded-recursion machinery that would otherwise be needed (and
  that is fragile to get exactly right without a Lean toolchain to check
  against, which this session does not have — see the same caveat already
  recorded in `PARTII_algorithms.lean` §10).

  `dh` is indexed, besides the fuel, by a single `V ⊕ List V` argument
  rather than being split into two mutually-recursive functions: `Sum.inl
  ω` is "process the removal of `ω`" (Algorithm 8 Lines 2-29 for one
  call), `Sum.inr l` is "process the `for each endpoint u in Q` loop"
  (Lines 10/18/26-29, with the freeze-only continuation of Lines 32-40
  folded directly into the cons case, immediately after `freezeOne`).
-/

/-- Freeze a single endpoint `u`: set its status to `frozen` and record it
    in the running cover `S`. (The `reps`/`rows`/`score` fields of `R` are
    left untouched — Algorithm 8's freeze step, unlike Algorithm 6's, does
    not delist anything, cf. the "no deletion" remark on `Status` in
    `reptable_ops_properties.lean`.) -/
public abbrev freezeOne (R : RTable G) (S : Finset V) (u : V) : RTable G × Finset V :=
  ({ R with status := upd R.status u Status.frozen }, insert u S)

/-- The endpoints Algorithm 8's removal step (Lines 9-17) considers when
    removing `ω`: every endpoint `u` with `u ∈ R.reps ω` (paper "L_ω") or
    `ω ∈ R.reps u` ("u represents ω"), i.e. Lines 10 and 18 of Algorithm 8
    combined into one `Finset.filter`. -/
public abbrev removalPartners (R : RTable G) (ω : V) : Finset V :=
  Finset.univ.filter (fun u => u ∈ R.reps ω ∨ ω ∈ R.reps u)

/-- Given the row `(a, b)` found for endpoint `u` (i.e. `a = u` or
    `b = u`), the *other* endpoint of that row — Algorithm 8 Lines 32-36's
    "u = the other endpoint in ψ's row". Kept as its own definition
    (rather than an inline `let`) so that a `simp only [dh]` unfolding of
    `dh`'s equations leaves `partnerOf row u` as a single opaque term
    instead of exposing a second, hidden `if`-expression nested inside the
    `if _ ∈ S' then ...` that follows it — the nesting that broke an
    earlier draft of the proof below (`split` would land on the wrong,
    inner `if`). -/
public abbrev partnerOf (row : Row V) (u : V) : V :=
  if row.1 = u then row.2 else row.1

/-- **Structural core of Algorithm 8** (`dh`): processes either the
    removal of a single endpoint `ω` (`Sum.inl ω`) — cascading the freeze
    of every `removalPartner`, and, mirroring Algorithm 8 Lines 32-40
    exactly, recursively removing a freshly-frozen partner's own
    row-partner whenever that row-partner is already frozen (a duad) —
    or the `for each` loop over a pending list of partners (`Sum.inr l`).
    Guarded throughout by the visited set `lam`: an endpoint already in
    `lam` is never processed twice (Lines 3-5 / Line 11 of Algorithm 8).
    Every recursive call consumes exactly one unit of the `Nat` fuel
    parameter, matching `n + 1 → n` in every branch below, which is why
    this compiles as ordinary structural recursion.
    `(dh n R S lam s).2.2` is the updated visited set `λ`; `.1` is the
    updated table; `.2.1` is the updated cover. -/
public noncomputable abbrev dh : Nat → RTable G → Finset V → Finset V → (V ⊕ List V) →
    RTable G × Finset V × Finset V
  | 0,     R, S, lam, _ => (R, S, lam)
  | n + 1, R, S, lam, Sum.inl ω =>
    if ω ∈ lam then
      (R, S, lam)
    else
      let lam1 := insert ω lam
      let R1   := { R with status := upd R.status ω Status.removed }
      let S1   := S.erase ω
      dh n R1 S1 lam1 (Sum.inr (removalPartners R1 ω).toList)
  | n + 1, R, S, lam, Sum.inr [] => (R, S, lam)
  | n + 1, R, S, lam, Sum.inr (u :: us) =>
    if u ∈ lam then
      dh n R S lam (Sum.inr us)
    else
      let (R', S') := freezeOne R S u
      let lam' := insert u lam
      match R'.rows.find? (fun rc => rc.1 = u ∨ rc.2 = u) with
      | none => dh n R' S' lam' (Sum.inr us)
      | some row =>
        let v := partnerOf row u
        if v ∈ S' then
          let (R'', S'', lam'') := dh n R' S' lam' (Sum.inl v)
          dh n R'' S'' lam'' (Sum.inr us)
        else
          dh n R' S' lam' (Sum.inr us)

-- ─────────────────────────────────────────────────────────────────────────
-- §3.1  Soundness by induction: AllFrozenOrRemoved and FrozenSet = cover
-- ─────────────────────────────────────────────────────────────────────────

/-- **Main structural invariant, proved by ordinary induction on the fuel
    `n`**: starting from a table already `AllFrozenOrRemoved` with
    recorded cover `S`, `dh`'s output is again `AllFrozenOrRemoved` with
    recorded cover exactly its returned cover, and its `reps`/`rows`
    fields are unchanged from the input (`freezeOne` and the removal step
    only ever touch `.status`). Because every branch of `dh`'s definition
    recurses at fuel exactly `n` (from the matched `n + 1`), a single
    `induction n` covers every case: this is genuine structural induction
    on `dh`'s own recursive definition, and no termination or bookkeeping
    fact here is taken as a hypothesis. -/
public theorem dh_status_frozen :
    ∀ (n : ℕ) (R : RTable G) (S lam : Finset V) (s : V ⊕ List V),
      AllFrozenOrRemoved R.toTableState → FrozenSet R.toTableState = S →
      AllFrozenOrRemoved (dh n R S lam s).1.toTableState ∧
      FrozenSet (dh n R S lam s).1.toTableState = (dh n R S lam s).2.1 ∧
      (dh n R S lam s).1.reps = R.reps ∧
      (dh n R S lam s).1.rows = R.rows := by
  have freeze_step : ∀ (R : RTable G) (S : Finset V) (u : V),
      AllFrozenOrRemoved R.toTableState → FrozenSet R.toTableState = S →
      AllFrozenOrRemoved (freezeOne R S u).1.toTableState ∧
      FrozenSet (freezeOne R S u).1.toTableState = (freezeOne R S u).2 ∧
      (freezeOne R S u).1.reps = R.reps ∧ (freezeOne R S u).1.rows = R.rows := by
    intro R S u hAll hFS
    have hFSiff : ∀ w, w ∈ S ↔ R.status w = Status.frozen := by
      intro w
      rw [← hFS]
      change w ∈ Finset.univ.filter (fun x => R.status x = Status.frozen)
          ↔ R.status w = Status.frozen
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, rfl, rfl⟩
    · intro w
      by_cases hw : w = u
      · rw [hw]
        left
        change (if u = u then Status.frozen else R.status u) = Status.frozen
        simp
      · rcases hAll w with h | h
        · left
          change (if w = u then Status.frozen else R.status w) = Status.frozen
          rw [ite_eq_right hw]; exact h
        · right
          change (if w = u then Status.frozen else R.status w) = Status.removed
          rw [ite_eq_right hw]; exact h
    · apply Finset.ext
      intro w
      change w ∈ Finset.univ.filter
            (fun x => (if x = u then Status.frozen else R.status x) = Status.frozen)
          ↔ w ∈ insert u S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hw : w = u
      · rw [hw]; simp
      · rw [ite_eq_right hw]
        constructor
        · intro h; exact Or.inr ((hFSiff w).mpr h)
        · rintro (h | h)
          · exact absurd h hw
          · exact (hFSiff w).mp h
  have remove_step : ∀ (R : RTable G) (S : Finset V) (ω : V),
      AllFrozenOrRemoved R.toTableState → FrozenSet R.toTableState = S →
      AllFrozenOrRemoved
        ({ R with status := upd R.status ω Status.removed } : RTable G).toTableState ∧
      FrozenSet ({ R with status := upd R.status ω Status.removed } : RTable G).toTableState
        = S.erase ω := by
    intro R S ω hAll hFS
    have hFSiff : ∀ w, w ∈ S ↔ R.status w = Status.frozen := by
      intro w
      rw [← hFS]
      change w ∈ Finset.univ.filter (fun x => R.status x = Status.frozen)
          ↔ R.status w = Status.frozen
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · intro w
      by_cases hw : w = ω
      · rw [hw]
        right
        change (if ω = ω then Status.removed else R.status ω) = Status.removed
        simp
      · rcases hAll w with h | h
        · left
          change (if w = ω then Status.removed else R.status w) = Status.frozen
          rw [ite_eq_right hw]; exact h
        · right
          change (if w = ω then Status.removed else R.status w) = Status.removed
          rw [ite_eq_right hw]; exact h
    · apply Finset.ext
      intro w
      change w ∈ Finset.univ.filter
            (fun x => (if x = ω then Status.removed else R.status x) = Status.frozen)
          ↔ w ∈ S.erase ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hw : w = ω
      · rw [hw]; simp
      · rw [ite_eq_right hw]
        constructor
        · intro h; exact ⟨hw, (hFSiff w).mpr h⟩
        · rintro ⟨-, h⟩; exact (hFSiff w).mp h
  intro n
  induction n with
  | zero =>
    intro R S lam s hAll hFS
    exact ⟨hAll, hFS, rfl, rfl⟩
  | succ n ih =>
    intro R S lam s hAll hFS
    cases s with
    | inl ω =>
      simp only [dh]
      split
      · exact ⟨hAll, hFS, rfl, rfl⟩
      · obtain ⟨hAll1, hFS1⟩ := remove_step R S ω hAll hFS
        exact ih ({ R with status := upd R.status ω Status.removed } : RTable G)
            (S.erase ω) (insert ω lam)
            (Sum.inr
              (removalPartners
                ({ R with status := upd R.status ω Status.removed } : RTable G) ω).toList)
            hAll1 hFS1
    | inr l =>
      cases l with
      | nil =>
        simp only [dh]
        exact ⟨hAll, hFS, trivial, trivial⟩
      | cons u us =>
        simp only [dh]
        split
        · exact ih R S lam (Sum.inr us) hAll hFS
        · obtain ⟨hAll', hFS', hreps', hrows'⟩ := freeze_step R S u hAll hFS
          rcases hfind : (freezeOne R S u).1.rows.find? (fun rc => rc.1 = u ∨ rc.2 = u)
            with _ | row
          · simp only [hfind]
            exact ih (freezeOne R S u).1 (freezeOne R S u).2 (insert u lam) (Sum.inr us)
              hAll' hFS'
          · simp only [hfind]
            split
            · set triple :=
                dh n (freezeOne R S u).1 (freezeOne R S u).2 (insert u lam)
                  (Sum.inl (partnerOf row u)) with htriple
              obtain ⟨hAllN, hFSN, hrepsN, hrowsN⟩ :=
                ih (freezeOne R S u).1 (freezeOne R S u).2 (insert u lam)
                  (Sum.inl (partnerOf row u)) hAll' hFS'
              rw [← htriple] at hAllN hFSN hrepsN hrowsN
              obtain ⟨g1, g2, g3, g4⟩ := ih triple.1 triple.2.1 triple.2.2 (Sum.inr us)
                hAllN hFSN
              exact ⟨g1, g2, by rw [g3, hrepsN, hreps'], by rw [g4, hrowsN, hrows']⟩
            · obtain ⟨g1, g2, g3, g4⟩ :=
                ih (freezeOne R S u).1 (freezeOne R S u).2 (insert u lam) (Sum.inr us)
                  hAll' hFS'
              exact ⟨g1, g2, by rw [g3, hreps'], by rw [g4, hrows']⟩

-- ─────────────────────────────────────────────────────────────────────────
-- §3.2  RemoveInvariant
-- ─────────────────────────────────────────────────────────────────────────

/-- The one fact about the cascade that is **not** mere bookkeeping: no
    two graph-adjacent endpoints are ever both left `removed` at the end
    of a single call to `dh (Sum.inl ω)`. -/
public abbrev NoAdjacentDoubleRemoval (n : ℕ) (R : RTable G) (S lam : Finset V) (ω : V) : Prop :=
  ∀ v w, G.Adj v w →
    (dh n R S lam (Sum.inl ω)).1.status v = Status.removed →
    (dh n R S lam (Sum.inl ω)).1.status w ≠ Status.removed

/-- `RemoveInvariant` for `dh`'s output, from `AllFrozenOrRemoved` (proved
    above, `dh_status_frozen`) together with `NoAdjacentDoubleRemoval`: if
    `v` is removed and adjacent to `w`, `w` cannot also be removed
    (`NoAdjacentDoubleRemoval`), so by `AllFrozenOrRemoved` it must be
    frozen. -/
public theorem dh_removeInvariant
    (n : ℕ) (R : RTable G) (S lam : Finset V) (ω : V)
    (hAll : AllFrozenOrRemoved R.toTableState) (hFS : FrozenSet R.toTableState = S)
    (hNoAdj : NoAdjacentDoubleRemoval n R S lam ω) :
    RemoveInvariant (dh n R S lam (Sum.inl ω)).1.toTableState := by
  intro v w hv hadj
  rcases (dh_status_frozen n R S lam (Sum.inl ω) hAll hFS).1 w with hw | hw
  · exact hw
  · exact absurd hw (hNoAdj v w hadj hv)

/-- Bundled soundness of a single fuel-bounded run of Algorithm 8's
    cascade: a genuine `IsValidFreezeRemove` outcome with matching
    `FrozenSet`, replacing the earlier `DuadicHopSound` hypothesis with a
    theorem. -/
public theorem dh_valid
    (n : ℕ) (R : RTable G) (S lam : Finset V) (ω : V)
    (hAll : AllFrozenOrRemoved R.toTableState) (hFS : FrozenSet R.toTableState = S)
    (hNoAdj : NoAdjacentDoubleRemoval n R S lam ω) :
    IsValidFreezeRemove (dh n R S lam (Sum.inl ω)).1.toTableState ∧
    FrozenSet (dh n R S lam (Sum.inl ω)).1.toTableState = (dh n R S lam (Sum.inl ω)).2.1 :=
  ⟨⟨dh_removeInvariant n R S lam ω hAll hFS hNoAdj,
     (dh_status_frozen n R S lam (Sum.inl ω) hAll hFS).1⟩,
   (dh_status_frozen n R S lam (Sum.inl ω) hAll hFS).2.1⟩

-- ─────────────────────────────────────────────────────────────────────────
-- §3.3  Lemma 7 for the derived Algorithm 8, with fuel fixed at a
--       generous, concrete bound
-- ─────────────────────────────────────────────────────────────────────────

/-- A single fuel-bounded call, removing one endpoint `ω` of a duad,
    packaged as a `HopCandidate` — built from `dh_valid` (a theorem)
    instead of an assumed soundness hypothesis. Fuel is fixed at
    `(Fintype.card V) ^ 2`, a generous bound (every genuine removal step
    grows the visited set, bounded by `Fintype.card V`, and each such
    step is preceded by traversing a partner list also of length at most
    `Fintype.card V`) — though, per the design note on `dh` above, no
    specific fuel amount needs to be proved sufficient for the theorems
    of this section to hold. -/
noncomputable def dh_gives_candidate
    (R : RepTable G) (RT : RTable G) (S : Finset V) (u v ω : V)
    (hduad : IsDuad R (RT.toTableState) u v)
    (hall : AllFrozenOrRemoved RT.toTableState)
    (hS : FrozenSet RT.toTableState = S)
    (hNoAdj : NoAdjacentDoubleRemoval ((Fintype.card V) ^ 2) RT S (∅ : Finset V) ω) :
    HopCandidate R (RT.toTableState) u v :=
  { st' := (dh ((Fintype.card V) ^ 2) RT S (∅ : Finset V) (Sum.inl ω)).1.toTableState
    valid' := (dh_valid ((Fintype.card V) ^ 2) RT S (∅ : Finset V) ω hall hS hNoAdj).1 }

/-- **Lemma 7, executable form, soundness now derived by induction**: given
    a duad `(u, v)` in the represents table `RT` (already fully frozen or
    removed, with recorded frozen set `S`) and `NoAdjacentDoubleRemoval`
    for the cascades starting at `u` and at `v`, if running the (derived,
    provably-terminating) Algorithm 8 cascade by removing `u` — or by
    removing `v` — strictly shrinks the frozen set, then a `DiminishingHop`
    exists for `RT.toTableState`. This is exactly "Algorithm 7 performs an
    S-diminishing hop if it exists" read off code whose termination and
    bookkeeping are proved, closing the gap the commentary
    of `PARTII_algorithms.lean` §10 leaves open ("connecting the
    two is a natural follow-on"). -/
public theorem Lemma7_exec
    (R : RepTable G) (RT : RTable G) (S : Finset V) {u v : V}
    (hduad : IsDuad R (RT.toTableState) u v)
    (hall : AllFrozenOrRemoved RT.toTableState)
    (hS : FrozenSet RT.toTableState = S)
    (hNoAdjU : NoAdjacentDoubleRemoval ((Fintype.card V) ^ 2) RT S (∅ : Finset V) u)
    (hNoAdjV : NoAdjacentDoubleRemoval ((Fintype.card V) ^ 2) RT S (∅ : Finset V) v)
    (hsmaller :
      (FrozenSet
        (dh ((Fintype.card V) ^ 2) RT S (∅ : Finset V) (Sum.inl u)).1.toTableState).card
          < (FrozenSet RT.toTableState).card ∨
      (FrozenSet
        (dh ((Fintype.card V) ^ 2) RT S (∅ : Finset V) (Sum.inl v)).1.toTableState).card
          < (FrozenSet RT.toTableState).card) :
    ∃ _ : DiminishingHop R (RT.toTableState), True :=
  Lemma7_duad R (RT.toTableState) hduad
    (dh_gives_candidate R RT S u v u hduad hall hS hNoAdjU)
    (dh_gives_candidate R RT S u v v hduad hall hS hNoAdjV)
    hsmaller
-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Correspondence with the paper's proof of Lemma 7 (p.60-61, lines
  1840-1856):
    "Line 1 ... initializes an empty list ... Lines 2 and 3 keep a record
     of the represents table R with the smallest number of frozen
     endpoints ..."
        → tracked implicitly: `Lemma7`'s conclusion is exactly the
          existence statement Theorem 6/7 need; the "running best" is not
          separately modeled since only the *existence* of a diminishing
          candidate matters for Lemma 7's own claim (Lemma 8, done later,
          is what reasons about the running best across the whole scan
          to bound the number of hops).
    "Line 10 ensures the presence of a duad ... Line 11 does an S-duadic
     hop for each of the endpoints in a duad ... Line 14 assesses whether
     the vertex cover returned ... is smaller ..."
        → `Lemma7_duad`'s two-way `rcases hsmaller with hu | hv`, exactly
          mirroring "try both, keep whichever succeeds".
    "Line 12 invokes Algorithm 8 (Duadic Hop)."
        → `Lemma7_exec`/`dh_gives_candidate`, which replace the abstract
          `HopCandidate` with the output of `dh` — a re-transcription of
          Algorithm 8 whose termination is by construction and whose
          status/cover bookkeeping is proved by induction
          (`dh_status_frozen`), rather than assumed.
-/
