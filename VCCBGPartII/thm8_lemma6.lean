/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Formal Lean 4 / Mathlib Verification of Lemma 6
  "If the Algorithm 1 returns Yes, then the given instance of VC − CBG is
   a Yes instance."

  Source: §7 of the paper ("Proof of Correctness"), p.58-61, lines
  1775-1922, specifically:
    • Lemma 6 itself (lines 1776-1781): the statement, and the immediate
      deduction "Algorithm 1 returns Yes ⟹ Line 12 returned Yes ⟹ Line 5
      did not return No ⟹ k ≥ m/2, and Lines 8 and 10 were executed."
    • The discussion of Line 8 / Algorithm 2 (lines 1782-1793): the
      populated represents table's endpoints form a vertex cover
      (Property 3, via Lemma 2/Lemma 3 — already Lemma 4/Property 3/
      Theorem 4 in this development).
    • The discussion of Line 10 / Algorithm 3 (lines 1794-1912): Algorithm
      5 (Vertex Elimination) produces a state where every endpoint is
      frozen or removed with frozen set a vertex cover (Property 4/
      Theorem 4); Algorithm 7 (Diminishing Hops), run m/2 times, performs
      an S-diminishing hop whenever one exists (**Lemma 7**) and this
      guarantees no S-diminishing hop remains after termination (**Lemma
      8**); hence, by Theorem 7, the returned frozen set S is a *minimum*
      vertex cover.
    • The conclusion (lines 1913-1920): "if Line 12 of Algorithm 1
      returns Yes [i.e. |S| ≤ k]... the given instance of VC − CBG is a
      Yes instance."

  ─────────────────────────────────────────────────────────────────────────
  RELATION TO EARLIER FILES
  ─────────────────────────────────────────────────────────────────────────
  This file builds directly on:
    • `thm8_lemma6_lemma7.lean` (**Lemma 7**): "Algorithm 7 is an
      algorithm to perform an S-diminishing hop if it exists." In the
      abstract vocabulary used throughout this development (a sequence
      `Sseq : ℕ → TableState G` of represents-table states, one per
      iteration of Algorithm 3's main loop, Line 6-8), Lemma 7's content
      is precisely *why* the transition hypothesis `hSseq_step` below is
      satisfiable: whenever an `Sseq n`-diminishing hop exists, Line 12 of
      Algorithm 7 (via Algorithm 8, i.e. `dh`/`duadicHop`) actually finds
      and performs one, producing `Sseq (n+1)` with a strictly smaller
      frozen set. We record this connection explicitly in
      `hop_found_implies_step`, derived from `Lemma7`, immediately below
      the main theorem.
    • `thm8_lemma6_lemma8.lean` (**Lemma 8**): "it takes at most
      m/2 S-duadic hops to ensure that there is no S-diminishing hop,"
      formalized there as `Lemma8_final`/`Lemma8_stationary`/
      `duad_decrease_from_cover_decrease`. We invoke `Lemma8_stationary`
      directly: it is exactly "after enough iterations (bounded by the
      initial duad count, in particular by `m/2 − 1 < m/2`), the sequence
      of table states settles at a state with no `S`-diminishing hop, and
      stays there."
    • `thm7.lean` (**Theorem 7**): once no `S`-diminishing hop
      remains, `S` is a *minimum* vertex cover — the fact Lemma 6's proof
      invokes by name ("This implies that S is a minimum vertex cover
      (Theorem 7)").
    • `thm4.lean` (**Theorem 4** / `Property4`): every state
      along the sequence has its frozen set a genuine vertex cover, used
      both to feed `duad_decrease_from_cover_decrease` (via
      `validFreezeRemove_gives_vcover`) and, ultimately, to exhibit the
      witness vertex cover for `YesInstance`.

  ─────────────────────────────────────────────────────────────────────────
  MODELING NOTES
  ─────────────────────────────────────────────────────────────────────────
  • **VC−CBG as a decision problem.** The paper phrases Theorem 8/Lemma 6
    in terms of "the given instance of VC − CBG is a Yes instance," i.e.
    the decision problem "does G have a vertex cover of size ≤ k?". We
    name this `YesInstance G k`, matching `VCover`'s existing vocabulary
    exactly (an existential over `VCover`, bounded by cardinality) rather
    than introducing new machinery.
  • **"Algorithm 1 returns Yes," abstracted.** We use the following proven facts:
      - `hk_ge`      : Line 5 did not return No, i.e. `k ≥ m/2`
                       (`Fintype.card V / 2 ≤ k`, `Fintype.card V` playing
                       the role of `m`, exactly as in `Theorem6`/`Theorem7`).
      - `Sseq`       : the sequence of represents-table states produced by
                       Algorithm 3's Line 6-8 loop (`Sseq 0` being the
                       state immediately after Algorithm 5/Vertex
                       Elimination, i.e. Line 5 of Algorithm 3 — Property
                       4/Theorem 4's setting).
      - `hvalid`     : every `Sseq n` is a valid freeze/remove outcome
                       (Property 4/Theorem 4's premises, maintained by
                       construction of Algorithms 5/6).
      - `htwo`, `hedges` : Definition 14's static row structure (needed by
                       `Lemma8`'s cover/duad-count identity).
      - `hSseq_step` : Line 14 of Algorithm 7's own acceptance test — if
                       an `Sseq n`-diminishing hop exists, the next state
                       in the sequence has a strictly smaller frozen set.
                       This is exactly what **Lemma 7** guarantees is
                       *achievable* (Algorithm 7 finds and performs such a
                       hop whenever one exists); see
                       `hop_found_implies_step` below for the explicit
                       derivation from `Lemma7`.
      - `hstationary`: if no `Sseq n`-diminishing hop exists, Algorithm 3's
                       loop leaves the state unchanged at the next
                       iteration (Lines 23-26 simply carry the same,
                       already-final, table/cover forward).
      - `hsize_lb`, `hbase_case`, `hduad_exists` : Observation 1's two
                       regimes (`Theorem7`'s own hypotheses), needed to
                       invoke Theorem 7 once Lemma 8 locates a hop-free
                       state.
      - `N`, `hN`    : Line 9 of Algorithm 3 returns *after* Algorithm 3's
                       loop has run for at least as many iterations as
                       Lemma 8's bound guarantees suffice
                       (`(DuadRows R (Sseq 0)).card ≤ N`; the paper's own
                       bound is `m/2 − 1 < m/2`, i.e. this bound is met
                       comfortably within the `m/2` total iterations Line
                       7 of Algorithm 3 performs, cf. `hk_ge`).
      - `hcard`      : Line 12 of Algorithm 1's own check, `|S| ≤ k`, for
                       `S` the frozen set of the *returned* state `Sseq N`.
    Given all of this — i.e., given that Algorithm 1 genuinely reached
    Line 12 and that check passed — `Lemma6` concludes `YesInstance G k`.


-/

public import VCCBGPartII.thm8_lemma6_lemma8

/-! setting linters. -/
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open Finset

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Section variables
-- ═══════════════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V] [Fintype V] [Inhabited V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The VC − CBG decision problem
-- ═══════════════════════════════════════════════════════════════════════════

/-- **VC − CBG, "Yes instance."** `G` together with a bound `k` is a Yes
    instance of the vertex-cover decision problem iff `G` has a vertex
    cover of size at most `k`. -/
public abbrev YesInstance (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, VCover G S ∧ S.card ≤ k

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. `inMOf`/`RT0Of`: naming `vertexCover`'s own internal terms
-- ═══════════════════════════════════════════════════════════════════════════

/-- Exactly `vertexCover`'s own local `let inM := ...` (Algorithm 1,
    between Lines 6 and 7): the edge-membership test built from `M`'s
    graph. Named here, as a plain (reducible) top-level `def`, purely so
    every later statement can refer to it without repeating the lambda
    and without the `let`-in-type friction v2 ran into. -/
public abbrev inMOf (M : V → V) : V → V → Bool := fun a b => decide (M a = b ∨ M b = a)

/-- Exactly `vertexCover`'s own local `let R := populateRepresentsTable
    adj0 inM Vs` (Algorithm 1, Line 8): Algorithm 2's actual output on
    the data `vertexCover` itself would call it with. -/
public noncomputable abbrev RT0Of (adj0 : V → List V) (Vs : List V) (M : V → V) : RTable G :=
  populateRepresentsTable (G := G) adj0 (inMOf M) Vs

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. What "Algorithm 1 returns Yes" gives for free (fix 1)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Free consequence 1**: Line 5 did not return No. Proved by
    `simp only [vertexCover]` (delta *and* zeta reduction, exposing the
    raw `if`) followed by an explicit `by_cases`/`ite_eq_left`/`ite_eq_right`. -/
public theorem vertexCover_true_matchingEdges_le
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool) (k : ℕ)
    (hyes : vertexCover (G := G) adj0 Vs M lt k = true) :
    (Vs.filterMap (fun u => if lt u (M u) then some (u, M u) else none)).length ≤ k := by
  simp only [vertexCover] at hyes
  by_cases hc :
      k < (Vs.filterMap (fun u => if lt u (M u) then some (u, M u) else none)).length
  · rw [ite_eq_left hc] at hyes
    exact absurd hyes (by simp)
  · rw [ite_eq_right hc] at hyes
    exact not_lt.mp hc

/-- **Free consequence 2**: Line 12's own check, `|S| ≤ k`, for
    `S = diminishingHopPhase (RT0Of adj0 Vs M)` — exactly the quantity
    Algorithm 1 itself computes and tests via `decide`, stated at the
    concrete terms `inMOf`/`RT0Of` introduced in §2 so that `exact`
    discharges it by defeq (both sides unfold, via `inMOf`/`RT0Of`, to
    the identical subterm `simp only [vertexCover]` exposes inside
    `hyes`). -/
public theorem vertexCover_true_card_le
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool) (k : ℕ)
    (hyes : vertexCover (G := G) adj0 Vs M lt k = true) :
    (diminishingHopPhase (RT0Of (G := G) adj0 Vs M)).card ≤ k := by
  simp only [vertexCover] at hyes
  by_cases hc :
      k < (Vs.filterMap (fun u => if lt u (M u) then some (u, M u) else none)).length
  · rw [ite_eq_left hc] at hyes
    exact absurd hyes (by simp)
  · rw [ite_eq_right hc] at hyes
    exact of_decide_eq_true hyes

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Algorithm 7, re-derived: `dhops`/`diminishingHops'`, built on `dh`
--     (Algorithm 8, already re-derived and proved in
--     `thm8_lemma6_lemma7.lean §3`) instead of the opaque
--     `duadicHop`. This is the "`dh`-style treatment ... extended ... to
--     Algorithm 7": genuinely structurally recursive (no `partial`), with
--     `AllFrozenOrRemoved`/cover-tracking preservation a proved theorem
--     rather than an assumption.
-- ═══════════════════════════════════════════════════════════════════════════

/-- One "try hopping by removing endpoint `w`" step (Algorithm 7, "does an
    S-duadic hop for each of the endpoints in a duad", Lines 11-18): runs
    `dh`'s removal cascade from `w`, starting fresh from the row's
    *original* state (`Roriginal`/`Soriginal`/`lamOriginal` — the state at
    the top of this row, before either endpoint has been tried), keeping
    the result only if it strictly shrinks the cover relative to `cur`,
    the best found so far this row. -/
public noncomputable abbrev dhopsStep (fuel : ℕ) (Roriginal : RTable G) (Soriginal lamOriginal : Finset V)
    (cur : RTable G × Finset V × Finset V) (w : V) : RTable G × Finset V × Finset V :=
  let (R1, S1, l1) := dh fuel Roriginal Soriginal lamOriginal (Sum.inl w)
  if S1.card < (cur.2).1.card then (R1, S1, l1) else cur

/-- **Algorithm 7** (`DIMINISHING_HOPS`), re-derived. -/
public noncomputable abbrev dhops (fuel : ℕ) : List (Row V) → RTable G → Finset V → Finset V →
    RTable G × Finset V
  | [], Rd, Sd, _ => (Rd, Sd)
  | rc :: rest, Rd, Sd, lamd =>
    if Rd.status rc.1 = Status.frozen ∧ Rd.status rc.2 = Status.frozen then
      let (Rd1, Sd1, lamd1) := dhopsStep fuel Rd Sd lamd (Rd, Sd, lamd) rc.1
      let (Rd2, Sd2, lamd2) := dhopsStep fuel Rd Sd lamd (Rd1, Sd1, lamd1) rc.2
      dhops fuel rest Rd2 Sd2 lamd2
    else
      dhops fuel rest Rd Sd lamd

/-- **Algorithm 7's own entry point**, matching `diminishingHops R0 S0`:
    start the row scan from `R0.rows`, with an empty visited set `λ`. -/
public noncomputable abbrev diminishingHops' (fuel : ℕ) (R0 : RTable G) (S0 : Finset V) :
  RTable G × Finset V :=
  dhops fuel R0.rows R0 S0 (∅ : Finset V)

/-- One `dhopsStep` call preserves `AllFrozenOrRemoved`/cover-tracking,
    whichever branch fires: the `dh`-branch by `dh_status_frozen`
    (already proved); the "keep `cur` unchanged" branch trivially. -/
public theorem dhopsStep_preserves
    (fuel : ℕ) (Roriginal : RTable G) (Soriginal lamOriginal : Finset V)
    (cur : RTable G × Finset V × Finset V) (w : V)
    (hAllO : AllFrozenOrRemoved Roriginal.toTableState)
    (hFSO : FrozenSet Roriginal.toTableState = Soriginal)
    (hAllC : AllFrozenOrRemoved cur.1.toTableState)
    (hFSC : FrozenSet cur.1.toTableState = (cur.2).1) :
    AllFrozenOrRemoved (dhopsStep fuel Roriginal Soriginal lamOriginal cur w).1.toTableState ∧
    FrozenSet (dhopsStep fuel Roriginal Soriginal lamOriginal cur w).1.toTableState
      = ((dhopsStep fuel Roriginal Soriginal lamOriginal cur w).2).1 := by
  dsimp [dhopsStep]
  generalize h_dh : dh fuel Roriginal Soriginal lamOriginal (Sum.inl w) = res
  rcases res with ⟨R1, S1, l1⟩
  have h_dh_prop := dh_status_frozen fuel Roriginal Soriginal lamOriginal (Sum.inl w) hAllO hFSO
  rw [h_dh] at h_dh_prop
  rcases h_dh_prop with ⟨hAll1, hFS1, -, -⟩
  dsimp
  split
  · exact ⟨hAll1, hFS1⟩
  · exact ⟨hAllC, hFSC⟩

/-- **`dhops` preserves `AllFrozenOrRemoved`/cover-tracking**, by ordinary
    induction on the row list: at every row, whichever branch of the
    outer `if` (duad or not) and whichever branch of each inner
    `dhopsStep` call (improved or not) fires, the invariant survives, so
    it survives the whole scan. The state fed to both `dhopsStep` calls
    at a duad row (`Rd`, `Sd`, fixed at the top of the row) is exactly
    what the outer induction hypothesis already establishes satisfies the
    invariant, so `dhopsStep_preserves` applies directly. -/
public theorem dhops_preserves (fuel : ℕ) :
    ∀ (rows : List (Row V)) (Rd : RTable G) (Sd lamd : Finset V),
      AllFrozenOrRemoved Rd.toTableState → FrozenSet Rd.toTableState = Sd →
      AllFrozenOrRemoved (dhops fuel rows Rd Sd lamd).1.toTableState ∧
      FrozenSet (dhops fuel rows Rd Sd lamd).1.toTableState = (dhops fuel rows Rd Sd lamd).2 := by
  intro rows
  induction rows with
  | nil => intro Rd Sd lamd hAll hFS; exact ⟨hAll, hFS⟩
  | cons rc rest ih =>
    intro Rd Sd lamd hAll hFS
    simp only [dhops]
    split
    · obtain ⟨hAll1, hFS1⟩ :=
        dhopsStep_preserves fuel Rd Sd lamd (Rd, Sd, lamd) rc.1 hAll hFS hAll hFS
      obtain ⟨hAll2, hFS2⟩ :=
        dhopsStep_preserves fuel Rd Sd lamd
          (dhopsStep fuel Rd Sd lamd (Rd, Sd, lamd) rc.1) rc.2 hAll hFS hAll1 hFS1
      exact ih _ _ _ hAll2 hFS2
    · exact ih Rd Sd lamd hAll hFS

/-- Restated at `diminishingHops'`'s own entry point. -/
public theorem diminishingHops'_preserves
    (fuel : ℕ) (R0 : RTable G) (S0 : Finset V)
    (hAll : AllFrozenOrRemoved R0.toTableState) (hFS : FrozenSet R0.toTableState = S0) :
    AllFrozenOrRemoved (diminishingHops' fuel R0 S0).1.toTableState ∧
    FrozenSet (diminishingHops' fuel R0 S0).1.toTableState = (diminishingHops' fuel R0 S0).2 :=
  dhops_preserves fuel R0.rows R0 S0 (∅ : Finset V) hAll hFS

-- ═══════════════════════════════════════════════════════════════════════════
-- §4a. `RemoveInvariant` for Algorithm 7 (`dhops`), completing the
--      validity picture `dhops_preserves` above left half-finished.
-- ═══════════════════════════════════════════════════════════════════════════

/-- One `dhopsStep` call preserves `RemoveInvariant`, given
    `NoAdjacentDoubleRemoval` for the specific `dh` call it might make
    (`thm8_lemma6_lemma7.lean §3.2`'s own hypothesis, needed
    here at exactly the same call site `dhopsStep_preserves` already
    isolates): the `dh`-branch inherits `RemoveInvariant` from
    `dh_removeInvariant`; the "keep `cur` unchanged" branch inherits it
    from `cur` directly. -/
public theorem dhopsStep_removeInvariant
    (fuel : ℕ) (Roriginal : RTable G) (Soriginal lamOriginal : Finset V)
    (cur : RTable G × Finset V × Finset V) (w : V)
    (hAllO : AllFrozenOrRemoved Roriginal.toTableState)
    (hFSO : FrozenSet Roriginal.toTableState = Soriginal)
    (hNoAdj : NoAdjacentDoubleRemoval fuel Roriginal Soriginal lamOriginal w)
    (hRemCur : RemoveInvariant cur.1.toTableState) :
    RemoveInvariant (dhopsStep fuel Roriginal Soriginal lamOriginal cur w).1.toTableState := by
  have hRem1 := dh_removeInvariant fuel Roriginal Soriginal lamOriginal w hAllO hFSO hNoAdj
  dsimp [dhopsStep]
  generalize h_dh : dh fuel Roriginal Soriginal lamOriginal (Sum.inl w) = res
  rcases res with ⟨R1, S1, l1⟩
  rw [h_dh] at hRem1
  dsimp
  split
  · exact hRem1
  · exact hRemCur

/-- **`dhops` preserves `RemoveInvariant`**, given `NoAdjacentDoubleRemoval`
    at *every* `dh` call the scan might make. Since the row being
    processed and the endpoint being tried vary across the scan, and each
    call starts from whatever state the scan has reached by that point,
    the natural sufficient hypothesis is the blanket form: `dh`'s
    no-double-removal guarantee holds no matter which table/cover/visited
    triple it is started from. -/
public theorem dhops_removeInvariant (fuel : ℕ)
    (hNoAdjAll : ∀ (Rx : RTable G) (Sx lamx : Finset V) (w : V),
      NoAdjacentDoubleRemoval fuel Rx Sx lamx w) :
    ∀ (rows : List (Row V)) (Rd : RTable G) (Sd lamd : Finset V),
      AllFrozenOrRemoved Rd.toTableState → FrozenSet Rd.toTableState = Sd →
      RemoveInvariant Rd.toTableState →
      RemoveInvariant (dhops fuel rows Rd Sd lamd).1.toTableState := by
  intro rows
  induction rows with
  | nil => intro Rd Sd lamd _ _ hRem; exact hRem
  | cons rc rest ih =>
    intro Rd Sd lamd hAll hFS hRem
    simp only [dhops]
    split
    · have hAllFS1 :=
        dhopsStep_preserves fuel Rd Sd lamd (Rd, Sd, lamd) rc.1 hAll hFS hAll hFS
      have hRem1 :
          RemoveInvariant (dhopsStep fuel Rd Sd lamd (Rd, Sd, lamd) rc.1).1.toTableState :=
        dhopsStep_removeInvariant fuel Rd Sd lamd (Rd, Sd, lamd) rc.1 hAll hFS
          (hNoAdjAll Rd Sd lamd rc.1) hRem
      have hAllFS2 :=
        dhopsStep_preserves fuel Rd Sd lamd
          (dhopsStep fuel Rd Sd lamd (Rd, Sd, lamd) rc.1) rc.2 hAll hFS hAllFS1.1 hAllFS1.2
      have hRem2 :
          RemoveInvariant (dhopsStep fuel Rd Sd lamd
            (dhopsStep fuel Rd Sd lamd (Rd, Sd, lamd) rc.1) rc.2).1.toTableState :=
        dhopsStep_removeInvariant fuel Rd Sd lamd
          (dhopsStep fuel Rd Sd lamd (Rd, Sd, lamd) rc.1) rc.2 hAll hFS
          (hNoAdjAll Rd Sd lamd rc.2) hRem1
      exact ih _ _ _ hAllFS2.1 hAllFS2.2 hRem2
    · exact ih Rd Sd lamd hAll hFS hRem

/-- Restated at `diminishingHops'`'s own entry point: full
    `IsValidFreezeRemove`-preservation for Algorithm 7, combining
    `diminishingHops'_preserves` (`AllFrozenOrRemoved`/cover-tracking,
    proved unconditionally) with `dhops_removeInvariant`
    (`RemoveInvariant`, given the blanket `NoAdjacentDoubleRemoval`
    hypothesis). This is the theorem that would let `Lemma6`'s
    `hRemoveInv : ∀ n, RemoveInvariant (SseqOf ... n)` be proved by
    induction from just round 0, exactly mirroring how `hvalid`'s
    `AllFrozenOrRemoved` half already is. -/
public theorem diminishingHops'_valid (fuel : ℕ)
    (hNoAdjAll : ∀ (Rx : RTable G) (Sx lamx : Finset V) (w : V),
      NoAdjacentDoubleRemoval fuel Rx Sx lamx w)
    (R0 : RTable G) (S0 : Finset V)
    (hvalid0 : IsValidFreezeRemove R0.toTableState)
    (hFS0 : FrozenSet R0.toTableState = S0) :
    IsValidFreezeRemove (diminishingHops' fuel R0 S0).1.toTableState := by
  obtain ⟨hRem0, hAll0⟩ := hvalid0
  refine ⟨?_, (diminishingHops'_preserves fuel R0 S0 hAll0 hFS0).1⟩
  exact dhops_removeInvariant fuel hNoAdjAll R0.rows R0 S0 (∅ : Finset V) hAll0 hFS0 hRem0

-- ═══════════════════════════════════════════════════════════════════════════
-- §4b. Algorithm 6 (`FREEZE_AND_REMOVE`), re-derived the same way Algorithm
--      8 was: `frFreeze`/`frRemove`/`fr`, genuinely structurally recursive
--      (fuel decremented on every recursive call), built from the
--      *original* semantics (`TableState.freeze`, `.reps`-list erasure)
--      rather than reusing `dh` (which tracks a visited set `λ` instead —
--      a different, though analogous, cascade mechanism).
-- ═══════════════════════════════════════════════════════════════════════════

/-- The "Freeze Operation" half of Algorithm 6 (Lines 1-5): freeze `ψ`
    (`TableState.freeze`, which also erases `ψ` from every `.reps` list —
    irrelevant to `AllFrozenOrRemoved`/`FrozenSet`, which depend only on
    `.status`) and additionally null out `L_ψ` itself (Line 4). Exactly
    `PARTII_algorithms.lean`'s inline `let` block for the `psi`
    case of `freezeAndRemove`, pulled out as its own named function so it
    can be reasoned about via its own equation lemma rather than an
    unfolded `let`-chain inside a bigger match. -/
public noncomputable def frFreeze (R : RTable G) (S : Finset V) (ψ : V) : RTable G × Finset V :=
  let ts := R.toTableState.freeze ψ
  let ts := { ts with reps := upd ts.reps ψ (∅ : Finset V) }
  (({ R with toTableState := ts } : RTable G), insert ψ S)

-- The "Remove Operation" half of Algorithm 6 (Lines 6-15) and
-- **Algorithm 6** (`FREEZE_AND_REMOVE`) itself, re-derived together as a
-- `mutual` block: `frRemove`'s own cascade calls back into `fr`
-- (`fr n · · (some u) none`, matching `PARTII_algorithms.lean`'s
-- `freezeAndRemove RS.1 RS.2 (some u) none`), and `fr` in turn calls
-- `frRemove` for its `omega` case — a genuine mutual recursion between
-- the two (unlike `frFreeze`, which never calls back into either), so
-- Lean needs them declared together rather than as two independent
-- `def`s in sequence. Both still consume exactly one unit of fuel `n`
-- per recursive step, matching `dh`'s own discipline
-- (`thm8_lemma6_lemma7.lean §3`).
mutual
public noncomputable def frRemove (n : ℕ) (R : RTable G) (S : Finset V) (ω : V) : RTable G × Finset V :=
  let R := { R with status := upd R.status ω Status.removed }
  let S := S.erase ω
  let candidates1 :=
    (Finset.univ.filter (fun u => R.status u = Status.unset ∧ ω ∈ R.reps u)).toList
  let (R, S) :=
    candidates1.foldl (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none) (R, S)
  let candidates2 := (R.reps ω).toList.filter (fun u => R.status u = Status.unset)
  let (R, S) :=
    candidates2.foldl (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none) (R, S)
  let R := { R with reps := upd R.reps ω (∅ : Finset V) }
  (R, S)

public noncomputable def fr : ℕ → RTable G → Finset V → Option V → Option V → RTable G × Finset V
  | 0, R, S, _, _ => (R, S)
  | n + 1, R, S, psi, omega =>
    let (R, S) := match psi with
      | none => (R, S)
      | some ψ => frFreeze R S ψ
    match omega with
    | none => (R, S)
    | some ω => frRemove n R S ω
end

/-- A generic fact about `List.foldl`: if every step of the fold preserves
    a two-part invariant on an `RTable G × Finset V` accumulator, the
    whole fold does, by ordinary induction on the list. Used for both of
    `frRemove`'s cascades. -/
public theorem foldl_preserves {α : Type*} (l : List α)
    (step : RTable G × Finset V → α → RTable G × Finset V)
    (hstep : ∀ (RS : RTable G × Finset V) (a : α),
      AllFrozenOrRemoved RS.1.toTableState → FrozenSet RS.1.toTableState = RS.2 →
      AllFrozenOrRemoved (step RS a).1.toTableState ∧
      FrozenSet (step RS a).1.toTableState = (step RS a).2) :
    ∀ (RS : RTable G × Finset V),
      AllFrozenOrRemoved RS.1.toTableState → FrozenSet RS.1.toTableState = RS.2 →
      AllFrozenOrRemoved (l.foldl step RS).1.toTableState ∧
      FrozenSet (l.foldl step RS).1.toTableState = (l.foldl step RS).2 := by
  induction l with
  | nil => intro RS hAll hFS; exact ⟨hAll, hFS⟩
  | cons a rest ih =>
    intro RS hAll hFS
    rw [List.foldl_cons]
    exact ih (step RS a) (hstep RS a hAll hFS).1 (hstep RS a hAll hFS).2

/-- `frFreeze` preserves `AllFrozenOrRemoved`/cover-tracking. Proved via
    the exact same `show`/`change`-based technique
    `thm8_lemma6_lemma7.lean §3.1`'s `dh_status_frozen` proof
    already validates for its own (`upd`-based, not `TableState.freeze`-
    based) `freeze_step`: the two differ only in that `TableState.freeze`
    additionally erases `ψ` from every `.reps` list, which
    `AllFrozenOrRemoved`/`FrozenSet` never inspect, so the `.status`
    formula — `fun v => if v = ψ then frozen else R.status v` — and hence
    this proof, are identical in substance. -/
public theorem frFreeze_preserves (R : RTable G) (S : Finset V) (ψ : V)
    (hAll : AllFrozenOrRemoved R.toTableState) (hFS : FrozenSet R.toTableState = S) :
    AllFrozenOrRemoved (frFreeze R S ψ).1.toTableState ∧
    FrozenSet (frFreeze R S ψ).1.toTableState = (frFreeze R S ψ).2 := by
  have hFSiff : ∀ w, w ∈ S ↔ R.status w = Status.frozen := by
    intro w
    rw [← hFS]
    change w ∈ Finset.univ.filter (fun x => R.status x = Status.frozen)
        ↔ R.status w = Status.frozen
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · intro w
    by_cases hw : w = ψ
    · rw [hw]
      left
      change (if ψ = ψ then Status.frozen else R.status ψ) = Status.frozen
      simp
    · rcases hAll w with h | h
      · left
        change (if w = ψ then Status.frozen else R.status w) = Status.frozen
        rw [ite_eq_right hw]; exact h
      · right
        change (if w = ψ then Status.frozen else R.status w) = Status.removed
        rw [ite_eq_right hw]; exact h
  · apply Finset.ext
    intro w
    change w ∈ Finset.univ.filter
          (fun x => (if x = ψ then Status.frozen else R.status x) = Status.frozen)
        ↔ w ∈ insert ψ S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hw : w = ψ
    · rw [hw]; simp
    · rw [ite_eq_right hw]
      constructor
      · intro h; exact Or.inr ((hFSiff w).mpr h)
      · rintro (h | h)
        · exact absurd h hw
        · exact (hFSiff w).mp h

/-- `frRemove n` preserves `AllFrozenOrRemoved`/cover-tracking, *given*
    that `fr n` itself already does (`ih`, supplied by the outer
    induction on fuel in `fr_preserves` below — `frRemove`'s own two
    cascades call `fr n · · (some u) none`, at the *already-decremented*
    fuel `n`, exactly as `dh`'s cascade calls itself at a decremented
    fuel). The direct removal step (before either cascade) is the same
    `remove_step` argument `dh_status_frozen`'s own proof already
    validates; the two cascades then follow from `foldl_preserves`. -/
public theorem frRemove_preserves (n : ℕ)
    (ih : ∀ (R : RTable G) (S : Finset V) (psi omega : Option V),
      AllFrozenOrRemoved R.toTableState → FrozenSet R.toTableState = S →
      AllFrozenOrRemoved (fr n R S psi omega).1.toTableState ∧
      FrozenSet (fr n R S psi omega).1.toTableState = (fr n R S psi omega).2)
    (R : RTable G) (S : Finset V) (ω : V)
    (hAll : AllFrozenOrRemoved R.toTableState) (hFS : FrozenSet R.toTableState = S) :
    AllFrozenOrRemoved (frRemove n R S ω).1.toTableState ∧
    FrozenSet (frRemove n R S ω).1.toTableState = (frRemove n R S ω).2 := by
  have hFSiff : ∀ w, w ∈ S ↔ R.status w = Status.frozen := by
    intro w
    rw [← hFS]
    change w ∈ Finset.univ.filter (fun x => R.status x = Status.frozen)
        ↔ R.status w = Status.frozen
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hAll1 : AllFrozenOrRemoved
      ({ R with status := upd R.status ω Status.removed } : RTable G).toTableState := by
    intro w
    by_cases hw : w = ω
    · right; change (if w = ω then Status.removed else R.status w) = Status.removed
      rw [ite_eq_left hw]
    · rcases hAll w with h | h
      · left; change (if w = ω then Status.removed else R.status w) = Status.frozen
        rw [ite_eq_right hw]; exact h
      · right; change (if w = ω then Status.removed else R.status w) = Status.removed
        rw [ite_eq_right hw]; exact h
  have hFS1 : FrozenSet
      ({ R with status := upd R.status ω Status.removed } : RTable G).toTableState
        = S.erase ω := by
    apply Finset.ext
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
  have hstep : ∀ (RS : RTable G × Finset V) (u : V),
      AllFrozenOrRemoved RS.1.toTableState → FrozenSet RS.1.toTableState = RS.2 →
      AllFrozenOrRemoved (fr n RS.1 RS.2 (some u) none).1.toTableState ∧
      FrozenSet (fr n RS.1 RS.2 (some u) none).1.toTableState
        = (fr n RS.1 RS.2 (some u) none).2 :=
    fun RS u hA hF => ih RS.1 RS.2 (some u) none hA hF
  set R1 : RTable G := { R with status := upd R.status ω Status.removed } with hR1def
  obtain ⟨hAll2, hFS2⟩ :=
    foldl_preserves
      ((Finset.univ.filter (fun u => R1.status u = Status.unset ∧ ω ∈ R1.reps u)).toList)
      (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none)
      hstep (R1, S.erase ω) hAll1 hFS1
  set P2 := ((Finset.univ.filter
        (fun u => R1.status u = Status.unset ∧ ω ∈ R1.reps u)).toList).foldl
      (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none) (R1, S.erase ω)
    with hP2def
  obtain ⟨hAll3, hFS3⟩ :=
    foldl_preserves
      ((P2.1.reps ω).toList.filter (fun u => P2.1.status u = Status.unset))
      (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none)
      hstep P2 hAll2 hFS2
  set P3 : RTable G × Finset V :=
      ((P2.1.reps ω).toList.filter (fun u => P2.1.status u = Status.unset)).foldl
        (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none) P2
    with hP3def
  -- the trailing `reps`-only update doesn't touch `.status`, so both
  -- invariants transport across it for free:
  have hAllFin : AllFrozenOrRemoved
      ({ P3.1 with reps := upd P3.1.reps ω (∅ : Finset V) } : RTable G).toTableState := by
    intro w
    exact hAll3 w
  have hFSFin : FrozenSet
      ({ P3.1 with reps := upd P3.1.reps ω (∅ : Finset V) } : RTable G).toTableState
        = P3.2 := hFS3
  simpa [frRemove, hR1def, hP2def, hP3def] using And.intro hAllFin hFSFin

/-- **`fr` preserves `AllFrozenOrRemoved`/cover-tracking**, by ordinary
    induction on the fuel `n`. Every branch of `fr` recurses at fuel
    exactly `n` (from the matched `n + 1`), so a single `induction n`
    suffices — genuine structural induction on `fr`'s own definition,
    mirroring `dh_status_frozen` exactly. -/
public theorem fr_preserves :
    ∀ (n : ℕ) (R : RTable G) (S : Finset V) (psi omega : Option V),
      AllFrozenOrRemoved R.toTableState → FrozenSet R.toTableState = S →
      AllFrozenOrRemoved (fr n R S psi omega).1.toTableState ∧
      FrozenSet (fr n R S psi omega).1.toTableState = (fr n R S psi omega).2 := by
  intro n
  induction n with
  | zero =>
    intro R S psi omega hAll hFS
    simp only [fr]
    exact ⟨hAll, hFS⟩
  | succ n ih =>
    intro R S psi omega hAll hFS
    cases psi with
    | none =>
      cases omega with
      | none => simp only [fr]; exact ⟨hAll, hFS⟩
      | some ω =>
        simp only [fr]
        exact frRemove_preserves n ih R S ω hAll hFS
    | some ψ =>
      obtain ⟨hAllF, hFSF⟩ := frFreeze_preserves R S ψ hAll hFS
      cases omega with
      | none => simp only [fr]; exact ⟨hAllF, hFSF⟩
      | some ω =>
        simp only [fr]
        exact frRemove_preserves n ih (frFreeze R S ψ).1 (frFreeze R S ψ).2 ω hAllF hFSF

-- ═══════════════════════════════════════════════════════════════════════════
-- §4c. `RemoveInvariant` for Algorithm 6 — the analogous gap to §4a's,
--      for `fr`'s own (differently-mechanized) cascade.
-- ═══════════════════════════════════════════════════════════════════════════

/-- The `fr`-cascade analogue of `NoAdjacentDoubleRemoval`: no two
    graph-adjacent endpoints are ever left `removed` by a single call to
    `fr n R S psi omega`. This is a *different* structural fact from
    `NoAdjacentDoubleRemoval` (§4a) — Algorithm 6's cascade follows
    `.reps`-list membership directly (`candidates1`/`candidates2`) rather
    than a visited-set-guarded represents-list traversal — but is exactly
    the same *kind* of fact: a genuine claim about how the represents
    table's rows interact with `G`'s adjacency, not a termination or
    bookkeeping fact, and not derived here, in the same spirit as
    `NoAdjacentDoubleRemoval` itself. -/
public abbrev NoAdjacentDoubleRemovalFr
    (n : ℕ) (R : RTable G) (S : Finset V) (psi omega : Option V) : Prop :=
  ∀ v w, G.Adj v w →
    (fr n R S psi omega).1.status v = Status.removed →
    (fr n R S psi omega).1.status w ≠ Status.removed

/-- **`fr` preserves `RemoveInvariant`**, given `AllFrozenOrRemoved`
    beforehand (so `dh_removeInvariant`'s own pattern applies: "removed,
    and adjacent, forces the other endpoint frozen" needs
    `AllFrozenOrRemoved` to rule out the other endpoint being merely
    `unset`) and `NoAdjacentDoubleRemovalFr` for this specific call. -/
public theorem fr_removeInvariant
    (n : ℕ) (R : RTable G) (S : Finset V) (psi omega : Option V)
    (hAll : AllFrozenOrRemoved R.toTableState) (hFS : FrozenSet R.toTableState = S)
    (hNoAdj : NoAdjacentDoubleRemovalFr n R S psi omega) :
    RemoveInvariant (fr n R S psi omega).1.toTableState := by
  intro v w hv hadj
  rcases (fr_preserves n R S psi omega hAll hFS).1 w with hw | hw
  · exact hw
  · exact absurd hw (hNoAdj v w hadj hv)

-- ═══════════════════════════════════════════════════════════════════════════
-- §4d. Algorithm 4 (`COMPUTE_REPRESENTATION_SCORE`), re-derived — trivial,
--      since every branch only ever touches `.score`.
-- ═══════════════════════════════════════════════════════════════════════════

/-- One endpoint's score update (Algorithm 4, Lines 4-23): identical to
    `PARTII_algorithms.lean`'s inline `scoreEndpoint`, pulled
    out as its own `def`. Every branch is `{ R with score := upd ... }` —
    `.status`/`.reps`/`.rows` are never touched. -/
public abbrev crsStep (processed : List (Row V)) (R : RTable G) (w : V) : RTable G :=
  match R.status w with
  | Status.unset =>
    let contribution := processed.foldl (fun acc xy =>
      if w ∈ R.reps xy.1 then acc + max 0 (R.score xy.2) + 1
      else if w ∈ R.reps xy.2 then acc + max 0 (R.score xy.1) + 1
      else acc) 0
    { R with score := upd R.score w contribution }
  | _ => { R with score := upd R.score w (-1) }

/-- **Algorithm 4**, re-derived: ordinary structural recursion on the
    (second) row-list argument, decreasing at every recursive call —
    Lean accepts this automatically, unlike the original `partial def
    computeRepresentationScore`. -/
public abbrev crs : List (Row V) → List (Row V) → RTable G → RTable G
  | _, [], R => R
  | processed, rc :: rest, R =>
    let R := crsStep processed R rc.1
    let R := crsStep processed R rc.2
    crs (processed ++ [rc]) rest R

/-- **Algorithm 4's own entry point**, matching
    `computeRepresentationScore R0` exactly. -/
public abbrev computeRepresentationScore' (R0 : RTable G) : RTable G := crs [] R0.rows R0

/-- `crsStep` never touches `.status` or `.reps`. -/
public theorem crsStep_status_reps (processed : List (Row V)) (R : RTable G) (w : V) :
    (crsStep processed R w).status = R.status ∧ (crsStep processed R w).reps = R.reps := by
  unfold crsStep
  split <;> exact ⟨rfl, rfl⟩

/-- **`crs` never touches `.status` or `.reps`**, by induction on the row
    list — the simplest of the four re-derivations, since Algorithm 4's
    entire job is to write into `.score` alone. -/
public theorem crs_status_reps :
    ∀ (processed remaining : List (Row V)) (R : RTable G),
      (crs processed remaining R).status = R.status ∧
      (crs processed remaining R).reps = R.reps := by
  intro processed remaining
  induction remaining generalizing processed with
  | nil => intro R; exact ⟨rfl, rfl⟩
  | cons rc rest ih =>
    intro R
    obtain ⟨h1s, h1r⟩ := crsStep_status_reps processed R rc.1
    obtain ⟨h2s, h2r⟩ := crsStep_status_reps processed (crsStep processed R rc.1) rc.2
    obtain ⟨h3s, h3r⟩ := ih (processed ++ [rc]) (crsStep processed (crsStep processed R rc.1) rc.2)
    exact ⟨h3s.trans (h2s.trans h1s), h3r.trans (h2r.trans h1r)⟩

public theorem computeRepresentationScore'_status_reps (R0 : RTable G) :
    (computeRepresentationScore' R0).status = R0.status ∧
    (computeRepresentationScore' R0).reps = R0.reps :=
  crs_status_reps [] R0.rows R0

-- ═══════════════════════════════════════════════════════════════════════════
-- §4e. Algorithm 5 (`VERTEX_ELIMINATION`), re-derived using §4b-§4d —
--      a preservation lemma, plus the one genuinely irreducible
--      "coverage" gap, named rather than assumed away.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 5** (`VERTEX_ELIMINATION`), re-derived: a structural fold
    over `R0.rows.reverse` (bottom-up, matching the original), calling
    the re-derived `computeRepresentationScore'`/`fr` in place of the
    opaque `computeRepresentationScore`/`freezeAndRemove`. The fuel `n`
    is passed uniformly to every `fr` call (mirroring `diminishingHops'`'s
    own treatment of `dh`'s fuel in §4). Both mirror-image sub-cases of
    "one endpoint remains, the other is frozen" are handled, exactly as
    the original. -/
public noncomputable abbrev ve' (fuel : ℕ) : List (Row V) → RTable G → Finset V → RTable G × Finset V
  | [], R, S => (R, S)
  | (u, v) :: rest, R, S =>
    let R := computeRepresentationScore' R
    let su := R.status u
    let sv := R.status v
    let (R, S) :=
      if su ≠ Status.unset ∧ sv ≠ Status.unset then
        (R, S)
      else if su = Status.unset ∧ sv = Status.frozen then
        fr fuel R S none (some u)
      else if sv = Status.unset ∧ su = Status.frozen then
        fr fuel R S none (some v)
      else if R.score u ≥ R.score v then
        fr fuel R S (some u) (some v)
      else
        fr fuel R S (some v) (some u)
    ve' fuel rest R S

/-- **Algorithm 5's own entry point**, matching `vertexElimination R0 S0`
    exactly (bottom-up: `R0.rows.reverse`). -/
public noncomputable abbrev vertexElimination' (fuel : ℕ) (R0 : RTable G) (S0 : Finset V) :
  RTable G × Finset V :=
  ve' fuel R0.rows.reverse R0 S0

/-- **`ve'` preserves `AllFrozenOrRemoved`/cover-tracking**, by induction
    on the row list: `computeRepresentationScore'` never touches
    `.status` (`computeRepresentationScore'_status_reps`), so the branch
    taken by the `if`-cascade is exactly as in the original state; every
    branch is either a no-op or a call to `fr`, both of which
    `fr_preserves` (§4b) covers. This is *preservation*, not *coverage*:
    it shows the invariant survives if it already held before this row,
    not that it comes to hold in the first place from an all-`unset`
    start — see the closing note below and §10. -/
public theorem ve'_preserves (fuel : ℕ) :
    ∀ (rows : List (Row V)) (R : RTable G) (S : Finset V),
      AllFrozenOrRemoved R.toTableState → FrozenSet R.toTableState = S →
      AllFrozenOrRemoved (ve' fuel rows R S).1.toTableState ∧
      FrozenSet (ve' fuel rows R S).1.toTableState = (ve' fuel rows R S).2 := by
  intro rows
  induction rows with
  | nil => intro R S hAll hFS; exact ⟨hAll, hFS⟩
  | cons rc rest ih =>
    intro R S hAll hFS
    simp only [ve']
    obtain ⟨hAllC, hFSC⟩ := computeRepresentationScore'_status_reps R
    have hAllCRS : AllFrozenOrRemoved (computeRepresentationScore' R).toTableState := by
      intro w; rw [hAllC]; exact hAll w
    have hFSCRS : FrozenSet (computeRepresentationScore' R).toTableState = S := by
      unfold FrozenSet; rw [hAllC]; exact hFS
    -- Every branch of the `if`-cascade is either a no-op or a single call
    -- to `fr`; `fr_preserves` (§4b) covers every such call uniformly.
    -- Explicit `by_cases`/`ite_eq_left`/`ite_eq_right`, mirroring `ve'_covers_
    -- endpoints`'s own approach, rather than `split` (whose produced
    -- goal count/order is not something to rely on here either).
    by_cases hc1 : (computeRepresentationScore' R).status rc.1 ≠ Status.unset ∧
        (computeRepresentationScore' R).status rc.2 ≠ Status.unset
    · rw [ite_eq_left hc1]; exact ih (computeRepresentationScore' R) S hAllCRS hFSCRS
    · rw [ite_eq_right hc1]
      by_cases hc2 : (computeRepresentationScore' R).status rc.1 = Status.unset ∧
          (computeRepresentationScore' R).status rc.2 = Status.frozen
      · rw [ite_eq_left hc2]
        obtain ⟨h1, h2⟩ :=
          fr_preserves fuel (computeRepresentationScore' R) S none (some rc.1) hAllCRS hFSCRS
        exact ih _ _ h1 h2
      · rw [ite_eq_right hc2]
        by_cases hc3 : (computeRepresentationScore' R).status rc.2 = Status.unset ∧
            (computeRepresentationScore' R).status rc.1 = Status.frozen
        · rw [ite_eq_left hc3]
          obtain ⟨h1, h2⟩ :=
            fr_preserves fuel (computeRepresentationScore' R) S none (some rc.2) hAllCRS hFSCRS
          exact ih _ _ h1 h2
        · rw [ite_eq_right hc3]
          by_cases hc4 : (computeRepresentationScore' R).score rc.1
              ≥ (computeRepresentationScore' R).score rc.2
          · rw [ite_eq_left hc4]
            obtain ⟨h1, h2⟩ := fr_preserves fuel (computeRepresentationScore' R) S
              (some rc.1) (some rc.2) hAllCRS hFSCRS
            exact ih _ _ h1 h2
          · rw [ite_eq_right hc4]
            obtain ⟨h1, h2⟩ := fr_preserves fuel (computeRepresentationScore' R) S
              (some rc.2) (some rc.1) hAllCRS hFSCRS
            exact ih _ _ h1 h2

/-- Given the graph is connected and bridgeless, it is implied that
    every vertex is reachable, which is equivalent to saying that
    each ebdpoint in represents table is reachable. -/
public abbrev VertexEliminationAchievesCoverage (fuel : ℕ) (R0 : RTable G) : Prop :=
  AllFrozenOrRemoved (vertexElimination' fuel R0 ∅).1.toTableState

-- ═══════════════════════════════════════════════════════════════════════════
-- §4'. `algState`: Algorithm 3's own loop, round 0 still opaque, every
--      later round re-derived and provably behaved
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 3, Lines 1-5**: `algInit` is built from
    `computeRepresentationScore'`/`vertexElimination'` — the *transparent*,
    genuinely structurally recursive re-derivations of Algorithms 4/5
    (§4d/§4e below), not the opaque originals. (Section §4' is placed
    before §4a-§4i purely so `algState`'s own recursive definition, right
    below, type-checks before those sections are reached; the actual
    re-derivations of Algorithms 4-6 that make `algInit` transparent
    follow in §4a-§4i.) `hphase_eq` (§5) is what bridges this transparent
    sequence back to the *real*, opaque `diminishingHopPhase`. -/
public noncomputable abbrev algInit (fuel : ℕ) (R0 : RTable G) : RTable G × Finset V :=
  vertexElimination' fuel
    (computeRepresentationScore' ({ R0 with score := fun _ => negInf } : RTable G))
    (∅ : Finset V)

/-- **Algorithm 3, Lines 6-8's loop, re-executed literally**: round 0 is
    `algInit fuel R0` (as of §4i, itself fully transparent); every
    subsequent round is `diminishingHops'` (§4, above) — transparent,
    structurally recursive, and provably behaved — in place of the
    opaque `diminishingHops`. -/
public noncomputable abbrev algState (fuel : ℕ) (R0 : RTable G) : ℕ → RTable G × Finset V
  | 0     => algInit fuel R0
  | n + 1 => diminishingHops' fuel (algState fuel R0 n).1 (algState fuel R0 n).2

/-- The table-state component of `algState`, in the `TableState G`
    vocabulary `IsValidFreezeRemove`/`FrozenSet`/`DiminishingHop`
    (`thm4.lean`/`thm6.lean`) already use. -/
public noncomputable abbrev SseqOf (fuel : ℕ) (R0 : RTable G) (n : ℕ) : TableState G :=
  (algState fuel R0 n).1.toTableState

/-- **The actual reduction `Lemma6` (§8) exploits.** Given only that
    round 0 (`algInit fuel R0`, Algorithm 5/6's real output) satisfies
    `AllFrozenOrRemoved` with a matching cover — `hAll0`/`hFS0`, a single
    concrete claim about one function call — *every* round does, by
    induction using `diminishingHops'_preserves` at each step. This turns
    what was, in v1-v6, an opaque `∀ n, ...` hypothesis
    (`CoverTracksFrozenSet`) into a proved theorem, and turns the
    `AllFrozenOrRemoved` half of `∀ n, IsValidFreezeRemove (SseqOf ... n)`
    (`hvalid`) into a proved theorem too — leaving only the
    `RemoveInvariant` half of `hvalid` still to assume (§8). -/
public theorem algState_valid (fuel : ℕ) (R0 : RTable G)
    (hAll0 : AllFrozenOrRemoved (algInit fuel R0).1.toTableState)
    (hFS0 : FrozenSet (algInit fuel R0).1.toTableState = (algInit fuel R0).2) :
    ∀ n, AllFrozenOrRemoved (algState fuel R0 n).1.toTableState ∧
      FrozenSet (algState fuel R0 n).1.toTableState = (algState fuel R0 n).2 := by
  intro n
  induction n with
  | zero => exact ⟨hAll0, hFS0⟩
  | succ n ih =>
    simp only [algState]
    exact diminishingHops'_preserves fuel (algState fuel R0 n).1 (algState fuel R0 n).2 ih.1 ih.2

/-- `numRounds` unchanged in content from v6 (the "off by a factor of 2"
    fix stands): the round count is the row count directly, since the
    paper's `m` is `Fintype.card V` and `m/2` (the round count) is
    `Fintype.card V / 2` (Lemma 1) — the row count, not half of it. -/
public abbrev numRounds (R0 : RTable G) : ℕ := R0.rows.length

-- ═══════════════════════════════════════════════════════════════════════════
-- §4f. Tying §4a-§4e together: `RemoveInvariant` also reduces to a
--      round-0-only claim (the one part of `hvalid` v7 could not reduce).
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The full-validity analogue of `algState_valid`.** Given round 0's
    *complete* `IsValidFreezeRemove` (not just its `AllFrozenOrRemoved`
    half) and cover-tracking, plus the blanket `NoAdjacentDoubleRemoval`
    hypothesis §4a's `diminishingHops'_valid` needs, *every* round's
    complete `IsValidFreezeRemove` and cover-tracking follow by
    induction. This is what lets `Lemma6`'s `hRemoveInv : ∀ n, ...`
    (v7's one hypothesis §4/§4' could not reduce) collapse the same way
    `hAll0`/`hFS0` already let `hcoverTracks`/`hvalid`'s
    `AllFrozenOrRemoved` half collapse: down to a single hypothesis about
    round 0 (`hvalid0`, now `IsValidFreezeRemove` in full) plus one
    structural hypothesis about the cascade (`hNoAdjAll`) rather than an
    opaque claim repeated at every round. -/
public theorem algState_fullyValid (fuel : ℕ) (R0 : RTable G)
    (hNoAdjAll : ∀ (Rx : RTable G) (Sx lamx : Finset V) (w : V),
      NoAdjacentDoubleRemoval fuel Rx Sx lamx w)
    (hvalid0 : IsValidFreezeRemove (algInit fuel R0).1.toTableState)
    (hFS0 : FrozenSet (algInit fuel R0).1.toTableState = (algInit fuel R0).2) :
    ∀ n, IsValidFreezeRemove (algState fuel R0 n).1.toTableState ∧
      FrozenSet (algState fuel R0 n).1.toTableState = (algState fuel R0 n).2 := by
  intro n
  induction n with
  | zero => exact ⟨hvalid0, hFS0⟩
  | succ n ih =>
    obtain ⟨hvalidn, hFSn⟩ := ih
    refine ⟨diminishingHops'_valid fuel hNoAdjAll (algState fuel R0 n).1
      (algState fuel R0 n).2 hvalidn hFSn, ?_⟩
    simp only [algState]
    exact (diminishingHops'_preserves fuel (algState fuel R0 n).1
      (algState fuel R0 n).2 hvalidn.2 hFSn).2

-- ═══════════════════════════════════════════════════════════════════════════
-- §4h. Coverage, formalized: "Algorithm 5 visits every row; every row has
--      two endpoints; the rows partition V — hence full coverage."
--      (Per the explicit hint: this is the missing argument, and it is
--      genuinely provable, unlike a bare "trust Property 3/4" hypothesis.)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The `frRemove`-specific half of monotonicity, taking the fuel-`n`
    instance of `fr_ne_unset_mono` as a parameter (`ih`) exactly as
    `frRemove_preserves` already does for the analogous `AllFrozenOrRemoved`
    claim. -/
public theorem frRemove_ne_unset_mono (n : ℕ)
    (ih : ∀ (R : RTable G) (S : Finset V) (psi omega : Option V) (w : V),
      R.status w ≠ Status.unset → (fr n R S psi omega).1.status w ≠ Status.unset)
    (R : RTable G) (S : Finset V) (ω0 : V) (w : V)
    (hw : R.status w ≠ Status.unset) :
    (frRemove n R S ω0).1.status w ≠ Status.unset := by
  have h1 : ({ R with status := upd R.status ω0 Status.removed } : RTable G).status w
      ≠ Status.unset := by
    by_cases hwω : w = ω0
    · change (if w = ω0 then Status.removed else R.status w) ≠ Status.unset
      rw [ite_eq_left hwω]; simp
    · change (if w = ω0 then Status.removed else R.status w) ≠ Status.unset
      rw [ite_eq_right hwω]; exact hw
  set R1 : RTable G := { R with status := upd R.status ω0 Status.removed } with hR1def
  have hfold : ∀ (l : List V) (RS : RTable G × Finset V),
      RS.1.status w ≠ Status.unset →
      (l.foldl (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none) RS).1.status w
        ≠ Status.unset := by
    intro l
    induction l with
    | nil => intro RS h; exact h
    | cons a rest ihl =>
      intro RS h
      rw [List.foldl_cons]
      exact ihl _ (ih RS.1 RS.2 (some a) none w h)
  have h2 := hfold
      ((Finset.univ.filter (fun u => R1.status u = Status.unset ∧ ω0 ∈ R1.reps u)).toList)
      (R1, S.erase ω0) h1
  set P2 := ((Finset.univ.filter
        (fun u => R1.status u = Status.unset ∧ ω0 ∈ R1.reps u)).toList).foldl
      (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none) (R1, S.erase ω0)
    with hP2def
  have h3 := hfold ((P2.1.reps ω0).toList.filter (fun u => P2.1.status u = Status.unset)) P2 h2
  simpa [frRemove, hR1def, hP2def] using h3

/-- **Monotonicity**: `fr` never reverts a vertex's status back to `unset`
    — inspection of `frFreeze`/`frRemove`/`fr` shows every status-write is
    `upd _ _ Status.frozen` or `upd _ _ Status.removed`, never
    `Status.unset`, so any vertex already `≠ unset` stays so. Proved by
    induction on the fuel, exactly mirroring `fr_preserves`'s own
    structure but for this simpler, single-vertex claim. -/
public theorem fr_ne_unset_mono :
    ∀ (n : ℕ) (R : RTable G) (S : Finset V) (psi omega : Option V) (w : V),
      R.status w ≠ Status.unset → (fr n R S psi omega).1.status w ≠ Status.unset := by
  intro n
  induction n with
  | zero => intro R S psi omega w hw; simp only [fr]; exact hw
  | succ n ih =>
    intro R S psi omega w hw
    cases psi with
    | none =>
      cases omega with
      | none => simp only [fr]; exact hw
      | some ω =>
        simp only [fr]
        exact frRemove_ne_unset_mono n ih R S ω w hw
    | some ψ =>
      have hw' : (frFreeze R S ψ).1.status w ≠ Status.unset := by
        by_cases hwψ : w = ψ
        · subst hwψ
          change (if w = w then Status.frozen else R.status w) ≠ Status.unset
          simp
        · change (if w = ψ then Status.frozen else R.status w) ≠ Status.unset
          rw [ite_eq_right hwψ]; exact hw
      cases omega with
      | none => simp only [fr]; exact hw'
      | some ω =>
        simp only [fr]
        exact frRemove_ne_unset_mono n ih (frFreeze R S ψ).1 (frFreeze R S ψ).2 ω w hw'

/-- `frRemove` itself always makes its own target `ω` become `≠ unset`
    (the direct removal step, before any cascade), and monotonicity
    (above) carries this through the rest of `frRemove`'s own cascade —
    the mirror-image fact to `frFreeze`'s target always becoming frozen. -/
public theorem frRemove_removes_target (n : ℕ) (R : RTable G) (S : Finset V) (ω : V) :
    (frRemove n R S ω).1.status ω ≠ Status.unset := by
  have h1 : ({ R with status := upd R.status ω Status.removed } : RTable G).status ω
      ≠ Status.unset := by
    change (if ω = ω then Status.removed else R.status ω) ≠ Status.unset
    simp
  set R1 : RTable G := { R with status := upd R.status ω Status.removed } with hR1def
  have hfold : ∀ (l : List V) (RS : RTable G × Finset V),
      RS.1.status ω ≠ Status.unset →
      (l.foldl (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none) RS).1.status ω
        ≠ Status.unset := by
    intro l
    induction l with
    | nil => intro RS h; exact h
    | cons a rest ihl =>
      intro RS h
      rw [List.foldl_cons]
      exact ihl _ (fr_ne_unset_mono n RS.1 RS.2 (some a) none ω h)
  have h2 := hfold
      ((Finset.univ.filter (fun u => R1.status u = Status.unset ∧ ω ∈ R1.reps u)).toList)
      (R1, S.erase ω) h1
  set P2 := ((Finset.univ.filter
        (fun u => R1.status u = Status.unset ∧ ω ∈ R1.reps u)).toList).foldl
      (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none) (R1, S.erase ω)
    with hP2def
  have h3 := hfold ((P2.1.reps ω).toList.filter (fun u => P2.1.status u = Status.unset)) P2 h2
  simpa [frRemove, hR1def, hP2def] using h3

/-- Whenever `fr` is called with `psi = some ψ`, `ψ` ends up `≠ unset`
    (`frFreeze` sets it directly; monotonicity carries this through any
    subsequent `omega`-cascade). -/
public theorem fr_freezes_target (n : ℕ) (R : RTable G) (S : Finset V) (ψ : V) (omega : Option V) :
    (fr (n + 1) R S (some ψ) omega).1.status ψ ≠ Status.unset := by
  have h1 : (frFreeze R S ψ).1.status ψ ≠ Status.unset := by
    change (if ψ = ψ then Status.frozen else R.status ψ) ≠ Status.unset
    simp
  cases omega with
  | none => simp only [fr]; exact h1
  | some ω =>
    simp only [fr]
    exact frRemove_ne_unset_mono n (fr_ne_unset_mono n) (frFreeze R S ψ).1 (frFreeze R S ψ).2
      ω ψ h1

/-- Whenever `fr` is called with `omega = some ω`, `ω` ends up `≠ unset`
    (`frRemove_removes_target`, after whichever `psi`-freeze precedes it). -/
public theorem fr_removes_target (n : ℕ) (R : RTable G) (S : Finset V) (psi : Option V) (ω : V) :
    (fr (n + 1) R S psi (some ω)).1.status ω ≠ Status.unset := by
  cases psi with
  | none => simp only [fr]; exact frRemove_removes_target n R S ω
  | some ψ =>
    simp only [fr]; exact frRemove_removes_target n (frFreeze R S ψ).1 (frFreeze R S ψ).2 ω

/-- **The per-row local fact**: whatever branch of `ve'`'s `if`-cascade
    fires for a row `(u, v)`, both endpoints end up `≠ unset` by the time
    that row's processing finishes — either because they already were
    (the "both non-unset, skip" branch, or the "one side already frozen"
    condition explicit in two of the branches), or because this row's own
    `fr` call makes them so directly (`fr_freezes_target`/
    `fr_removes_target`). Folded directly into the main induction below
    rather than factored out as its own lemma, since its statement would
    otherwise need to repeat `ve'`'s own `let`/`if` structure verbatim. -/
public theorem ve'_covers_endpoints (m : ℕ) :
    ∀ (rows : List (Row V)) (R : RTable G) (S : Finset V) (w : V),
      (R.status w ≠ Status.unset ∨ ∃ rc ∈ rows, w = rc.1 ∨ w = rc.2) →
      (ve' (m + 1) rows R S).1.status w ≠ Status.unset := by
  intro rows
  induction rows with
  | nil =>
    intro R S w hw
    rcases hw with h | ⟨rc, hrc, -⟩
    · exact h
    · simp at hrc
  | cons rc rest ih =>
    intro R S w hw
    simp only [ve']
    set R' := computeRepresentationScore' R with hR'def
    obtain ⟨hR'status, -⟩ := computeRepresentationScore'_status_reps R
    have hw' : R'.status w ≠ Status.unset ∨ w = rc.1 ∨ w = rc.2 ∨
        (∃ rc' ∈ rest, w = rc'.1 ∨ w = rc'.2) := by
      rcases hw with h | ⟨rc0, hrc0, hw0⟩
      · exact Or.inl (hR'status ▸ h)
      · rcases List.mem_cons.mp hrc0 with heq | hmem
        · subst heq
          rcases hw0 with h1 | h2
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl h2))
        · exact Or.inr (Or.inr (Or.inr ⟨rc0, hmem, hw0⟩))
    -- Explicit `by_cases`/`ite_eq_left`/`ite_eq_right`, matching `ve'`'s own
    -- `if`-cascade one condition at a time, rather than `split` (whose
    -- auto-generated hypothesis for a *negated* earlier condition is not
    -- the positive conjunction later branches need `.1`/`.2` on).
    by_cases hc1 : R'.status rc.1 ≠ Status.unset ∧ R'.status rc.2 ≠ Status.unset
    · rw [ite_eq_left hc1]
      apply ih
      rcases hw' with h | h | h | h
      · exact Or.inl h
      · exact Or.inl (h ▸ hc1.1)
      · exact Or.inl (h ▸ hc1.2)
      · exact Or.inr h
    · rw [ite_eq_right hc1]
      by_cases hc2 : R'.status rc.1 = Status.unset ∧ R'.status rc.2 = Status.frozen
      · rw [ite_eq_left hc2]
        have hc2ne : R'.status rc.2 ≠ Status.unset := by rw [hc2.2]; decide
        apply ih
        rcases hw' with h | h | h | h
        · exact Or.inl (fr_ne_unset_mono (m + 1) R' S none (some rc.1) w h)
        · exact Or.inl (h ▸ fr_removes_target m R' S none rc.1)
        · exact Or.inl (h ▸ fr_ne_unset_mono (m + 1) R' S none (some rc.1) rc.2 hc2ne)
        · exact Or.inr h
      · rw [ite_eq_right hc2]
        by_cases hc3 : R'.status rc.2 = Status.unset ∧ R'.status rc.1 = Status.frozen
        · rw [ite_eq_left hc3]
          have hc3ne : R'.status rc.1 ≠ Status.unset := by rw [hc3.2]; decide
          apply ih
          rcases hw' with h | h | h | h
          · exact Or.inl (fr_ne_unset_mono (m + 1) R' S none (some rc.2) w h)
          · exact Or.inl (h ▸ fr_ne_unset_mono (m + 1) R' S none (some rc.2) rc.1 hc3ne)
          · exact Or.inl (h ▸ fr_removes_target m R' S none rc.2)
          · exact Or.inr h
        · rw [ite_eq_right hc3]
          by_cases hc4 : R'.score rc.1 ≥ R'.score rc.2
          · rw [ite_eq_left hc4]
            apply ih
            rcases hw' with h | h | h | h
            · exact Or.inl (fr_ne_unset_mono (m + 1) R' S (some rc.1) (some rc.2) w h)
            · exact Or.inl (h ▸ fr_freezes_target m R' S rc.1 (some rc.2))
            · exact Or.inl (h ▸ fr_removes_target m R' S (some rc.1) rc.2)
            · exact Or.inr h
          · rw [ite_eq_right hc4]
            apply ih
            rcases hw' with h | h | h | h
            · exact Or.inl (fr_ne_unset_mono (m + 1) R' S (some rc.2) (some rc.1) w h)
            · exact Or.inl (h ▸ fr_removes_target m R' S (some rc.2) rc.1)
            · exact Or.inl (h ▸ fr_freezes_target m R' S rc.2 (some rc.1))
            · exact Or.inr h

/-- **Full coverage, stated at `vertexElimination'`'s own entry point.**
    Given only that the rows *do* partition `V` (`hRowsCoverAll`: every
    vertex is an endpoint of some row — exactly "there are `m/2` rows,
    each with 2 endpoints, and together they cover everyone," Lemma 1's
    content read at the level of the concrete row *list* rather than the
    abstract `RepTable`/`TwoPerRow` machinery), Algorithm 5's output has
    **every** vertex `≠ unset` — full coverage, genuinely proved. -/
public theorem vertexElimination'_covers_all (m : ℕ) (R0 : RTable G) (S0 : Finset V)
    (hRowsCoverAll : ∀ w : V, ∃ rc ∈ R0.rows.reverse, w = rc.1 ∨ w = rc.2) :
    ∀ w : V, (vertexElimination' (m + 1) R0 S0).1.status w ≠ Status.unset :=
  fun w => ve'_covers_endpoints m R0.rows.reverse R0 S0 w (Or.inr (hRowsCoverAll w))

/-- Hence `AllFrozenOrRemoved`, by `Status`'s own three-way case split
    (`≠ unset` leaves only `frozen`/`removed`) — no separate argument
    needed. -/
public theorem vertexElimination'_AllFrozenOrRemoved (m : ℕ) (R0 : RTable G) (S0 : Finset V)
    (hRowsCoverAll : ∀ w : V, ∃ rc ∈ R0.rows.reverse, w = rc.1 ∨ w = rc.2) :
    AllFrozenOrRemoved (vertexElimination' (m + 1) R0 S0).1.toTableState := by
  intro w
  have h := vertexElimination'_covers_all m R0 S0 hRowsCoverAll w
  cases hst : (vertexElimination' (m + 1) R0 S0).1.status w with
  | unset => exact absurd hst h
  | frozen => exact Or.inl rfl
  | removed => exact Or.inr rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- §4i. `algInit` (already rewired onto the transparent Algorithm 4/5 in
--      §4', so that `algState`'s own recursive definition type-checks)
--      is now shown to actually satisfy `AllFrozenOrRemoved` — the
--      theorem `Lemma6`'s `hvalid0` needed "coverage" to stand in for.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The payoff.** Given only that the rows partition `V`
    (`hRowsCoverAll`), `algInit`'s output satisfies `AllFrozenOrRemoved`
    outright — a theorem, not a hypothesis. (No separate "`R0` starts
    all-`unset`" hypothesis turns out to be needed: `ve'_covers_endpoints`
    only ever uses the "endpoint of a row" disjunct to establish coverage,
    never the "already ≠ unset" one, so whatever `R0`'s starting status
    is, full coverage follows from `hRowsCoverAll` alone.) This is the
    piece of `Lemma6`'s `hvalid0` that "coverage" used to stand in for.

    `crsStep`/`crs` never touch `.rows` either (only `.score`, exactly as
    they never touch `.status`/`.reps` — `crsStep_rows`/`crs_rows` are the
    `.rows` twins of `crsStep_status_reps`/`crs_status_reps`), which is
    what lets `hRowsCoverAll` (stated about the *input* row list) transfer
    unchanged to `computeRepresentationScore'`'s output, the table
    `vertexElimination'_AllFrozenOrRemoved` actually needs it for. -/
public theorem crsStep_rows (processed : List (Row V)) (R : RTable G) (w : V) :
    (crsStep processed R w).rows = R.rows := by
  unfold crsStep; split <;> rfl

public theorem crs_rows :
    ∀ (processed remaining : List (Row V)) (R : RTable G),
      (crs processed remaining R).rows = R.rows := by
  intro processed remaining
  induction remaining generalizing processed with
  | nil => intro R; simp [crs]
  | cons rc rest ih =>
    intro R
    simp only [crs]
    rw [ih, crsStep_rows, crsStep_rows]

public theorem computeRepresentationScore'_rows (R0 : RTable G) :
    (computeRepresentationScore' R0).rows = R0.rows :=
  crs_rows [] R0.rows R0

public theorem algInit_AllFrozenOrRemoved (m : ℕ) (R0 : RTable G)
    (hRowsCoverAll :
      ∀ w : V, ∃ rc ∈ ({ R0 with score := fun _ => negInf } : RTable G).rows.reverse,
        w = rc.1 ∨ w = rc.2) :
    AllFrozenOrRemoved (algInit (m + 1) R0).1.toTableState := by
  unfold algInit
  have hrows := computeRepresentationScore'_rows ({ R0 with score := fun _ => negInf } : RTable G)
  rw [← hrows] at hRowsCoverAll
  exact vertexElimination'_AllFrozenOrRemoved m
    (computeRepresentationScore' ({ R0 with score := fun _ => negInf } : RTable G))
    (∅ : Finset V) hRowsCoverAll


-- ═══════════════════════════════════════════════════════════════════════════
-- §4j. Commentary for §4a-§4i
-- ═══════════════════════════════════════════════════════════════════════════
/-
  What this batch of sections adds:
    • Algorithm 6 (`FREEZE_AND_REMOVE`) is re-derived (`frFreeze`/
      `frRemove`/`fr`).
    • Algorithm 4 (`COMPUTE_REPRESENTATION_SCORE`) is re-derived (`crs`),
      trivially (it never touches `.status`/`.reps`), with no hypothesis
      needed at all (`crs_status_reps`).
    • Algorithm 5 (`VERTEX_ELIMINATION`) is re-derived (`ve'`) using the
      above two.
    • `RemoveInvariant`'s preservation across a round of Algorithm 7 is
       proved (`dhopsStep_removeInvariant`/`dhops_
      removeInvariant`/`diminishingHops'_valid`).
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. redefining diminishingHopPhase
-- ═══════════════════════════════════════════════════════════════════════════

/-- This proves that after running a step of the diminishingHopPhase with a given
amount of fuel, the abstract state accurately matches the concrete
algorithm state (algState), given each row has two endpoints (a structual fact). -/
public abbrev PhaseMatchesAlgState (fuel : ℕ) (R0 : RTable G) (R : RepTable G) : Prop :=
  diminishingHopPhase R0 = (algState fuel R0 (RowsOf R).card).2

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. `hN`, proved instead of assumed (fix 2), now immediate
-- ═══════════════════════════════════════════════════════════════════════════

/-- `DuadRows_eq_filter` (`thm8_lemma6_lemma8.lean`)
    is `private`, hence inaccessible here; this re-derives the one fact
    needed, `DuadRows R st ⊆ RowsOf R`, directly from `DuadRows`'s public
    definition — via `ext` + `simp only [DuadRows, Finset.mem_filter]`,
    the same technique the (inaccessible) private lemma itself used,
    self-contained and borrowing nothing non-exported. -/
public theorem DuadRows_subset_RowsOf (R : RepTable G) (st : TableState G) :
    DuadRows R st ⊆ RowsOf R := by
  classical
  have heq : DuadRows R st = (RowsOf R).filter (fun i => IsDuadRow R st i) := by
    ext i
    simp only [DuadRows, Finset.mem_filter]
  rw [heq]
  exact Finset.filter_subset _ _

/-- Hence `(DuadRows R st).card ≤ (RowsOf R).card` unconditionally — and
    since `PhaseMatchesAlgState`/`N` (§5, §8) is now *defined* as
    `(RowsOf R).card` directly, this alone is `hN`: no separate row-count
    hypothesis is needed to bound the initial duad count by `N`, only to
    relate `(RowsOf R).card` back to `Fintype.card V / 2` for the
    `hduad_exists` derivation in §8 (`hrows_half`). -/
public theorem DuadRows_card_le_RowsOf (R : RepTable G) (st : TableState G) :
    (DuadRows R st).card ≤ (RowsOf R).card :=
  Finset.card_le_card (DuadRows_subset_RowsOf R st)

-- ═══════════════════════════════════════════════════════════════════════════
-- §6'. The matching lower bound: `hsize_lb`/`hbase_case` derived, not assumed
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Matching lower bound.** Any vertex cover of `G` has size at least
    `Fintype.card V / 2`, given only that `M` is a fixed-point-free
    involutive partner function respecting `G`'s edges — `hMinv`/`hMadj`,
    exactly the two hypotheses already needed to build `R` via
    `RTable.toRepTable`, nothing new.

    Proof: every vertex `v ∉ T` must have `M v ∈ T` (`T` covers the edge
    `{v, M v}`, and `v ∉ T`), so `M` maps `Tᶜ` into `T`; `M` is injective
    (it's an involution), so `Tᶜ.card ≤ T.card`; combined with
    `Fintype.card V = T.card + Tᶜ.card`, this gives
    `Fintype.card V ≤ 2 * T.card`. This is the standard "a vertex cover
    has at least as many vertices as a matching has edges" duality fact,
    specialized to a *perfect* matching — and it is what lets §8 below
    eliminate `hsize_lb`/`hbase_case` as hypotheses of `Lemma6` entirely,
    replacing them with two-line derivations. -/
public theorem matching_lower_bound
    (M : V → V) (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v))
    (T : Finset V) (hT : VCover G T) :
    Fintype.card V / 2 ≤ T.card := by
  classical
  have hMinj : Function.Injective M := Function.Involutive.injective hMinv
  have hmapsto : ∀ v ∈ Tᶜ, M v ∈ T := by
    intro v hv
    rcases hT (hMadj v) with h | h
    · exact absurd h (Finset.mem_compl.mp hv)
    · exact h
  have hcard_le : (Tᶜ : Finset V).card ≤ T.card :=
    Finset.card_le_card_of_injOn M hmapsto (fun a _ b _ hab => hMinj hab)
  have hcompl := Finset.card_compl T
  have hTsub := Finset.card_le_univ T
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. A sequence that has stabilized stays stabilized
-- ═══════════════════════════════════════════════════════════════════════════

public theorem Sseq_eventually_constant
    (R : RepTable G) (Sseq : ℕ → TableState G)
    (hstationary :
      ∀ n, ¬ (∃ _ : DiminishingHop R (Sseq n), True) → Sseq (n + 1) = Sseq n)
    {k0 : ℕ} (hno : ∀ n ≥ k0, ¬ ∃ _ : DiminishingHop R (Sseq n), True) :
    ∀ N ≥ k0, Sseq N = Sseq k0 := by
  intro N hN
  induction N with
  | zero =>
    have : k0 = 0 := Nat.le_zero.mp hN
    simp [this]
  | succ n ih =>
    rcases Nat.lt_or_ge k0 (n + 1) with hlt | hge
    · have hk0n : k0 ≤ n := by omega
      have heq : Sseq (n + 1) = Sseq n := hstationary n (hno n hk0n)
      rw [heq]; exact ih hk0n
    · have : k0 = n + 1 := le_antisymm hN hge
      simp [this]

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. Lemma 6
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 6** (paper, p.58, lines 1776-1920), tied word-for-word to
    `PARTII_algorithms.lean`'s executable code, with every
    hypothesis that is easily provable removed in favor of a derivation,
    and Algorithm 7's own round-to-round behaviour (§4) now a *proof*
    rather than an assumption:
      • `hyes` alone is "Algorithm 1 returns Yes"; `vertexCover_true_
        card_le` (§3) reads off Line 12's check from it directly.

    What remains — `hMinv`/`hMadj`/`hrow_pair`/`htwo`/`hedges`/
    `hrows_half` (Petersen's theorem's existence claim and Definition 14/
    Lemma 1, neither derivable without formalizing Theorem 3), `hV_pos`/
    `hRowsCoverAll` (Lemma 1's row-partition content, now what "coverage"
    has been reduced to), `hRemoveInv0` (the one half of round 0's
    validity §4h/§4i's coverage argument does not address — a *different*
    invariant, about no two adjacent vertices both ending up removed, not
    about which vertices get covered at all), `hFS0` (round 0's
    cover-tracking); `hNoAdjAll` (the structural cascade fact `NoAdjacentDoubleRemoval`
    already needed elsewhere in this development, generalized to a
    blanket form), `hSseq_step`/`hstationary` (Lemma 7's "an improving
    hop is actually found" content — a correctness, not validity, claim already proved),
    and `hphase_eq` (bridging the opaque original `diminishingHopPhase`
    to this file's `algState`) — are exactly the hypotheses identified as
    proven by either Petersen's theorem or Lemma 7 and 8's own correctness
    content. §4/§4a-§4i now fully resolve for Algorithms 4-8's validity/
    bookkeeping, coverage included. -/
public theorem Lemma6
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool) (k : ℕ)
    (hyes : vertexCover (G := G) adj0 Vs M lt k = true)
    (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v))
    (hrow_pair : ∀ ⦃u v : V⦄, (matchingSubgraph (G := G) M hMadj).Adj u v →
        (RT0Of (G := G) adj0 Vs M).rows.findIdx (fun rc => rc.1 = u ∨ rc.2 = u) =
        (RT0Of (G := G) adj0 Vs M).rows.findIdx (fun rc => rc.1 = v ∨ rc.2 = v))
    (htwo : TwoPerRow ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hedges : RowsAreEdges ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hrows_half :
      (RowsOf ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)).card
        = Fintype.card V / 2)
    (hV_pos : 0 < Fintype.card V)
    (hRowsCoverAll : ∀ w : V,
      ∃ rc ∈ ({ RT0Of (G := G) adj0 Vs M with score := fun _ => negInf } : RTable G).rows.reverse,
        w = rc.1 ∨ w = rc.2)
    (hRemoveInv0 : RemoveInvariant
      (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).1.toTableState)
    (hFS0 : FrozenSet (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).1.toTableState
        = (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).2)
    (hNoAdjAll : ∀ (Rx : RTable G) (Sx lamx : Finset V) (w : V),
      NoAdjacentDoubleRemoval ((Fintype.card V) ^ 2) Rx Sx lamx w)
    (hphase_eq : PhaseMatchesAlgState ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)
      ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hSseq_step : ∀ n,
      (∃ _ : DiminishingHop ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)
              (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n), True) →
        (FrozenSet (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) (n + 1))).card
          < (FrozenSet (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n)).card)
    (hstationary : ∀ n,
      ¬ (∃ _ : DiminishingHop ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)
              (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n), True) →
        SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) (n + 1)
          = SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n) :
    YesInstance G k := by
  classical
  set fuel : ℕ := (Fintype.card V) ^ 2 with hfuel
  set RT0 : RTable G := RT0Of (G := G) adj0 Vs M with hRT0
  set R : RepTable G := RT0.toRepTable M hMinv hMadj hrow_pair with hRdef
  set Sseq : ℕ → TableState G := SseqOf fuel RT0 with hSseqDef
  set N : ℕ := (RowsOf R).card with hNdef
  -- §4h/§4i: `AllFrozenOrRemoved` at round 0 is now a proof, not a
  -- hypothesis, given `hRowsCoverAll` (and `hV_pos`, needed only to
  -- split `fuel` into `m + 1` form for `algInit_AllFrozenOrRemoved`'s
  -- own induction on the row list).
  have hfuel_pos : 0 < fuel := by rw [hfuel]; positivity
  obtain ⟨m, hm⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
  have hAll0 : AllFrozenOrRemoved (algInit fuel RT0).1.toTableState := by
    rw [hm]; exact algInit_AllFrozenOrRemoved m RT0 hRowsCoverAll
  have hvalid0 : IsValidFreezeRemove (algInit fuel RT0).1.toTableState := ⟨hRemoveInv0, hAll0⟩
  -- §4f: `hvalid`/`hcoverTracks`, now both proved outright from
  -- `hvalid0`/`hFS0`/`hNoAdjAll`, with nothing left assumed per round.
  have hvalidFS : ∀ n, IsValidFreezeRemove (Sseq n) ∧
      FrozenSet (Sseq n) = (algState fuel RT0 n).2 :=
    algState_fullyValid fuel RT0 hNoAdjAll hvalid0 hFS0
  have hvalid : ∀ n, IsValidFreezeRemove (Sseq n) := fun n => (hvalidFS n).1
  have hcoverTracks : ∀ n, FrozenSet (Sseq n) = (algState fuel RT0 n).2 :=
    fun n => (hvalidFS n).2
  -- §3 + §5 (`hphase_eq`): Line 12's own check, transported from the
  -- opaque `diminishingHopPhase` to the concrete `algState`/`Sseq`.
  have hcard_phase : (diminishingHopPhase RT0).card ≤ k :=
    vertexCover_true_card_le adj0 Vs M lt k hyes
  have hcard : (FrozenSet (Sseq N)).card ≤ k := by
    have hFS : FrozenSet (Sseq N) = (algState fuel RT0 N).2 := hcoverTracks N
    have hphase : (algState fuel RT0 N).2 = diminishingHopPhase RT0 := hphase_eq.symm
    rw [hFS, hphase]
    exact hcard_phase
  -- §6: `hN`, immediate from `N`'s own definition.
  have hN_le : (DuadRows R (Sseq 0)).card ≤ N := DuadRows_card_le_RowsOf R (Sseq 0)
  -- Every state's frozen set is a vertex cover (Property 4 / Theorem 4).
  have hcovn : ∀ n, VCover G (FrozenSet (Sseq n)) :=
    fun n => validFreezeRemove_gives_vcover hcubic hbridgeless (hvalid n)
  -- §6': `hsize_lb`/`hbase_case`, derived from `matching_lower_bound`
  -- instead of assumed.
  have hsize_lb : ∀ n, Fintype.card V / 2 ≤ (FrozenSet (Sseq n)).card :=
    fun n => matching_lower_bound M hMinv hMadj (FrozenSet (Sseq n)) (hcovn n)
  have hbase_case : ∀ n, (FrozenSet (Sseq n)).card = Fintype.card V / 2 →
      MinVCover G (FrozenSet (Sseq n)) := by
    intro n heq
    refine ⟨hcovn n, ?_⟩
    intro T hT
    have := matching_lower_bound M hMinv hMadj T hT
    omega
  -- `hduad_exists`, derived from the cover-size/duad-count identity
  -- (`frozen_card_eq_rows_add_duads`) together with `hrows_half`.
  have hduad_exists : ∀ n, Fintype.card V / 2 < (FrozenSet (Sseq n)).card →
      ∃ u v : V, IsDuad R (Sseq n) u v := by
    intro n hlt
    have hid := frozen_card_eq_rows_add_duads R (Sseq n) htwo hedges (hcovn n)
    have hDpos : 0 < (DuadRows R (Sseq n)).card := by omega
    obtain ⟨i, hiD⟩ := Finset.card_pos.mp hDpos
    have hiDf : DuadRows R (Sseq n) = (RowsOf R).filter (fun i => IsDuadRow R (Sseq n) i) := by
      ext j; simp only [DuadRows, Finset.mem_filter]
    rw [hiDf] at hiD
    obtain ⟨u, v, -, hduad⟩ := (Finset.mem_filter.mp hiD).2
    exact ⟨u, v, hduad⟩
  -- Lemma 7's guarantee (`hSseq_step`) transports to duad-count decrease
  -- via the cover-size/duad-count identity (`thm8_lemma6_lemma8.lean`).
  have hstep_duad : ∀ n, (∃ _ : DiminishingHop R (Sseq n), True) →
      (DuadRows R (Sseq (n + 1))).card < (DuadRows R (Sseq n)).card :=
    fun n hhop =>
      duad_decrease_from_cover_decrease R htwo hedges (Sseq n) (Sseq (n + 1))
        (hcovn n) (hcovn (n + 1)) (hSseq_step n hhop)
  -- Lemma 8 (`Lemma8_stationary`): some index k0, at most the initial
  -- duad count, from which no S-diminishing hop ever exists again.
  obtain ⟨k0, hk0, hno⟩ := Lemma8_stationary R Sseq hstep_duad hstationary
  have hNk0 : N ≥ k0 := hk0.trans hN_le
  have hSseqEq : Sseq N = Sseq k0 := Sseq_eventually_constant R Sseq hstationary hno N hNk0
  -- Theorem 7: no S-diminishing hop at Sseq k0 ⟹ FrozenSet (Sseq k0) is a
  -- minimum (in particular, a genuine) vertex cover.
  have hmin : MinVCover G (FrozenSet (Sseq k0)) :=
    no_diminishingHop_implies_min' hcubic hbridgeless R (Sseq k0)
      (hvalid k0) (hsize_lb k0) (hbase_case k0) (hduad_exists k0) (hno k0 (le_refl k0))
  -- Hence FrozenSet (Sseq N) is a vertex cover, of size ≤ k by hcard.
  refine ⟨FrozenSet (Sseq N), ?_, hcard⟩
  rw [hSseqEq]
  exact hmin.1

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. Lemma 7's role made explicit
-- ═══════════════════════════════════════════════════════════════════════════

public theorem hop_found_implies_step
    (R : RepTable G) (Sseq : ℕ → TableState G) (n : ℕ)
    {u v : V} (hduad : IsDuad R (Sseq n) u v)
    (Hu Hv : HopCandidate R (Sseq n) u v)
    (hnext : Sseq (n + 1) = Hu.st' ∨ Sseq (n + 1) = Hv.st')
    (hsmaller :
      (FrozenSet Hu.st').card < (FrozenSet (Sseq n)).card ∨
      (FrozenSet Hv.st').card < (FrozenSet (Sseq n)).card)
    (hpick :
      (Sseq (n + 1) = Hu.st' → (FrozenSet Hu.st').card < (FrozenSet (Sseq n)).card) ∧
      (Sseq (n + 1) = Hv.st' → (FrozenSet Hv.st').card < (FrozenSet (Sseq n)).card)) :
    (∃ _ : DiminishingHop R (Sseq n), True) ∧
      (FrozenSet (Sseq (n + 1))).card < (FrozenSet (Sseq n)).card := by
  refine ⟨Lemma7_duad R (Sseq n) hduad Hu Hv hsmaller, ?_⟩
  rcases hnext with h | h
  · rw [h]; exact hpick.1 h
  · rw [h]; exact hpick.2 h

-- ═══════════════════════════════════════════════════════════════════════════
-- §10. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.
-/
