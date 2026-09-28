module
/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
/-
  Formal Lean 4 / Mathlib TRANSCRIPTION of Algorithms 1-8
  ("VERTEX_COVER", "POPULATE_REPRESENTS_TABLE", "DIMINISHING_HOP_PHASE",
   "COMPUTE_REPRESENTATION_SCORE", "VERTEX_ELIMINATION", "FREEZE_AND_REMOVE",
   "DIMINISHING_HOPS", "DUADIC_HOP")

  Source: §6 of the paper, pp.52-57 (lines 1741-1798), Algorithms 1-8.

  ─────────────────────────────────────────────────────────────────────────
  REUSE OF DEFINITIONS
  ─────────────────────────────────────────────────────────────────────────
  This file builds the algorithms directly on top of:
    • `Status`            (`unset`/`frozen`/`removed`)                — from
       `reptable_ops_properties.lean`.
    • `RepList G u`        (Definition 13's static represents list)     — same.
    • `TableState G`       (`status : V → Status`, `reps : V → Finset V`) — same.
    • `initialState G`      (`status := unset`, `reps := RepList G ·`)   — same;
       this is *exactly* Algorithm 2 Line 2's initial represents-table
       column data, so `RTable.empty` below is defined directly as
       `initialState G` plus the two extra bookkeeping columns Algorithm 3
       Line 2 adds (row order, score ζ).
    • `TableState.freeze`  — reused verbatim for the "Freeze Operation"
       half of Algorithm 6 (Lines 1-5): `TableState.freeze` already
       performs "freeze ψ" + "delist ψ from every represents list"
       (Lines 2, 5); we only need to additionally null out `L_ψ` itself
       (Line 4) after calling it.
    • `RepTable G` (`M : G.Subgraph`, `isPM`, `row : V → ℕ`, `row_pair`) — from
       `lemma4.lean`; Algorithm 2's output row list is packaged
       into an honest `RepTable G` value by `RTable.toRepTable` below,
       so that the algorithm's output can be fed directly into
       `Lemma4`/`Theorem4`/`Theorem6`/`Theorem7` from the rest of this
       development.
    • `VCover`, `MinVCover`, `FrozenSet`, `IsValidFreezeRemove`, `IsDuad`,
       `DiminishingHop`                                                 — from
       `thm4`/`thm6`/`thm7`, all still available (unused by the
       *executable* code below, but this is what a future correctness
       theorem connecting `vertexCover`'s output to `MinVCover` would sit
       on top of).

  Overall, this file defines executable (`partial def`) functions transcribing the pseudocode
  line-by-line.
-/

public import VCCBGPartII.thm7
/-! setting linters. -/
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Section variables
-- ═══════════════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V] [Fintype V] [Inhabited V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The represents table used by Algorithms 2-8: `TableState G`
--     (status, reps — reused verbatim) plus the two extra columns
--     Algorithm 3 Line 2 introduces (row order, score ζ).
-- ═══════════════════════════════════════════════════════════════════════════

/-- A row of the represents table: the two endpoints of one matching edge
    (Definition 14). Represents lists/status/score for these (and every
    other) endpoint live centrally in the enclosing table (`TableState`'s
    `reps`/`status`, plus `score` below), not per-row. -/
public abbrev Row (V : Type*) := V × V

/-- The represents table threaded through Algorithms 2-8: `TableState G`
    (reused verbatim: `status`, `reps`) extended with the row order and
    representation score Algorithm 3 adds. -/
public structure RTable (G : SimpleGraph V) extends TableState G where
  /-- Rows in insertion order = the paper's top-to-bottom table order. -/
  rows : List (Row V)
  /-- The representation score ζ_v (Algorithm 3 Line 3 onward). -/
  score : V → Int

/-- The `-∞` sentinel of Algorithm 3, Line 3. `Int` has no genuine `-∞`, so
    we use a value no honest score (bounded by table size) can reach. -/
public abbrev negInf : Int := -1000000000

/-- Algorithm 2, Lines 1-2's starting point: no rows yet, and the columns
    initialized exactly as `initialState G` already does (every endpoint
    `unset`, `reps = RepList` i.e. Definition 13's static represents
    list) — this *is* Algorithm 2 Line 2's "four-column table" before any
    row has been inserted, reusing `initialState` directly rather than
    re-deriving "start every endpoint's represents list at its full
    neighbor set". -/
public noncomputable def RTable.empty (G : SimpleGraph V) [DecidableRel G.Adj] : RTable G where
  toTableState := initialState G
  rows  := []
  score := fun _ => negInf

/-- Pointwise function update, `f[v ↦ a]`, used for "set endpoint v's
    column entry to a" (score column only — `status`/`reps` updates reuse
    `TableState.freeze`/direct field overrides below). -/
public abbrev upd {α : Type*} (f : V → α) (v : V) (a : α) : V → α :=
  fun w => if w = v then a else f w

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Algorithm 2 : POPULATE_REPRESENTS_TABLE(G, M, V_S)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Line 1: "T = an array of arrays storing sorted vertices at each level
    of a breadth-first search tree seeded on the first vertex in `V_S`".
    `adj` is the *current* (shrinking, Line 13) adjacency-list function
    used purely for BFS/edge-selection bookkeeping — distinct from the
    represents lists `reps`, which (per `initialState`/Definition 13)
    stay the *static* full neighbor sets throughout Phase II and are only
    ever mutated later, in Phase III, by `TableState.freeze`/the removal
    cascade of Algorithm 6. -/
public partial abbrev bfsLevels (adj : V → List V) (start : V) : List (List V) :=
  let rec go (frontier visited : List V) : List (List V) :=
    match frontier with
    | [] => []
    | _  =>
      let nbrs :=
        ((frontier.flatMap adj).eraseDups).filter
          (fun w => !(visited.contains w) && !(frontier.contains w))
      frontier :: go nbrs (visited ++ frontier)
  go [start] []

/-- Lines 6-9: find an `M`-edge from `u` to a vertex on the same level
    (Line 6-7), else to a vertex on the next level (Line 8-9). `inM u w`
    tests whether the edge `{u, w}` is one of the edges of `M`. -/
public abbrev selectMEdge (adj : V → List V) (inM : V → V → Bool)
    (u : V) (sameLevel nextLevel : List V) : Option V :=
  match (adj u).find? (fun w => inM u w && sameLevel.contains w) with
  | some w => some w
  | none   => (adj u).find? (fun w => inM u w && nextLevel.contains w)

/-- Line 13: "Remove from graph G the selected edge and all the edges that
    are connected to the two endpoints" — delete every edge incident to
    `x` from the (BFS-only) adjacency function. -/
public abbrev removeIncidentEdges (adj : V → List V) (x : V) : V → List V :=
  fun w => if w = x then [] else (adj w).filter (· ≠ x)

/-- Lines 3-16, the double loop ("for each level ... for each unvisited
    vertex u in level ..."), transcribed as two nested local recursions.
    Only `.rows` of the table is ever extended here (Line 12); `.reps`
    stays exactly the `RepList`-seeded value from `RTable.empty`, per the
    design note above. -/
public partial def populateLoop
    (inM : V → V → Bool)
    (levels : List (List V)) (adj : V → List V) (visited : List V) (R : RTable G) :
    RTable G :=
  match levels with
  | []             => R                                              -- Line 16 (outer end)
  | level :: rest  =>
    let nextLevel := rest.headD []
    -- Line 5: "for each unvisited vertex u in level do"
    let rec vertexLoop (vs : List V) (adj : V → List V) (visited : List V)
        (R : RTable G) : (V → List V) × List V × RTable G :=
      match vs with
      | []      => (adj, visited, R)
      | u :: us =>
        if visited.contains u then
          vertexLoop us adj visited R                                -- (u already visited: skip)
        else
          match selectMEdge adj inM u level nextLevel with
          | none   => vertexLoop us adj visited R                    -- no selectable edge yet
          | some w =>
            let visited := u :: w :: visited                          -- Line 11
            let R := { R with rows := R.rows ++ [(u, w)] }             -- Line 12
            let adj := removeIncidentEdges (removeIncidentEdges adj u) w  -- Line 13
            -- Line 14: any now-edgeless vertex is marked visited.
            let visited :=
              (Finset.univ.filter (fun z => adj z = [] ∧ ¬ visited.contains z)).toList
                ++ visited
            vertexLoop us adj visited R
    let (adj, visited, R) := vertexLoop level adj visited R
    populateLoop inM rest adj visited R

/-- **Algorithm 2** (`POPULATE_REPRESENTS_TABLE(G, M, V_S)`), returning an
    `RTable G` built on top of `RTable.empty` (i.e. `initialState G`,
    reusing `RepList`/`Status` from `reptable_ops_properties.lean`
    without re-deriving them). `M` enters only through `inM`, the
    edge-membership test used to steer BFS edge selection (Lines 6-9). -/
public abbrev populateRepresentsTable
    (adj0 : V → List V) (inM : V → V → Bool) (Vs : List V) : RTable G :=
  match Vs with
  | []      => RTable.empty G
  | v0 :: _ =>
    let T := bfsLevels adj0 v0                                        -- Line 1
    populateLoop inM T adj0 [] (RTable.empty G)                        -- Lines 2-16
    -- Line 17: return R (the result of `populateLoop`).

-- ═══════════════════════════════════════════════════════════════════════════
-- §2'. Packaging Algorithm 2's output as an honest `RepTable G`
--      (reusing `RepTable` from `lemma4.lean` verbatim).
-- ═══════════════════════════════════════════════════════════════════════════

/-- `M`, given as its total partner function, as a `G.Subgraph` — the
    bridge needed to reuse `RepTable G`'s `M : G.Subgraph` field (rather
    than re-deriving a `RepTable` from scratch). -/
public noncomputable abbrev matchingSubgraph (M : V → V) (hMadj : ∀ v, G.Adj v (M v)) :
    G.Subgraph where
  verts := Set.univ
  Adj   := fun u v => M u = v ∨ M v = u
  adj_sub := by
    rintro u v (h | h)
    · exact h ▸ hMadj u
    · exact h ▸ (hMadj v).symm
  edge_vert := fun _ => Set.mem_univ _
  symm := by
    constructor
    rintro u v (h | h)
    · exact Or.inr h
    · exact Or.inl h

/-- `matchingSubgraph` is a perfect matching whenever `M` is a total
    involutive partner function without fixed points (the standard
    "read off your partner" view of a perfect matching, reused wherever
    `RepTable.isPM` is needed). -/
public theorem matchingIsPerfectMatching
    (M : V → V) (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v)) :
    (matchingSubgraph (G := G) M hMadj).IsPerfectMatching := by
  refine ⟨fun v _ => ⟨M v, Or.inl rfl, ?_⟩, fun v => Set.mem_univ v⟩
  rintro w (h | h)
  · exact h.symm
  · have := hMinv w; rw [h] at this; exact this.symm

/-- Packages the row list built by `populateRepresentsTable` together with
    a perfect matching into a genuine `RepTable G` value (reusing
    `RepTable` from `lemma4.lean` verbatim), so Algorithm 2's
    output connects directly to `Lemma4`/`Theorem4`/`Theorem6`/`Theorem7`.
    `hrow_pair` — "the two endpoints inserted together into one row of
    `rows` get the same row index" — holds by construction of
    `populateLoop` (each row is inserted as a matched pair in a single
    step, Line 12) but, exactly as `hbridgeless`/`hcubic`/`ExactlyOneDuad`
    are taken as hypotheses elsewhere in this development rather than
    re-derived by induction on the algorithm's own loop, we take it here
    too. -/
public abbrev RTable.toRepTable (R : RTable G) (M : V → V)
    (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v))
    (hrow_pair : ∀ ⦃u v : V⦄, (matchingSubgraph (G := G) M hMadj).Adj u v →
      R.rows.findIdx (fun rc => rc.1 = u ∨ rc.2 = u) =
      R.rows.findIdx (fun rc => rc.1 = v ∨ rc.2 = v)) :
    RepTable G where
  M := matchingSubgraph M hMadj
  isPM := matchingIsPerfectMatching M hMinv hMadj
  row := fun w => R.rows.findIdx (fun rc => rc.1 = w ∨ rc.2 = w)
  row_pair := hrow_pair

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Algorithm 4 : COMPUTE_REPRESENTATION_SCORE(R)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 4**. Lines 2-26: single top-down pass over the rows,
    computing (or re-fixing, for frozen/removed endpoints) each endpoint's
    ζ from the ζ's of endpoints in rows strictly above it — since we fold
    top-down and update `R.score` as we go, those are already the
    freshly-recomputed values by the time `row` is reached, matching "for
    each row_j in R that is above row". `R.reps`/`R.status` here are
    exactly `TableState`'s fields (reused, not redefined). -/
public partial def computeRepresentationScore (R0 : RTable G) : RTable G :=
  let rec loop (processed : List (Row V)) (remaining : List (Row V)) (R : RTable G) :
      RTable G :=
    match remaining with
    | []              => R                                            -- Line 26 (outer end)
    | (u, v) :: rest  =>
      -- Lines 4-23, "for each endpoint u in row do" (executes exactly twice).
      let scoreEndpoint (w : V) (R : RTable G) : RTable G :=
        match R.status w with
        | Status.frozen  => { R with score := upd R.score w (-1) }     -- Lines 5-7
        | Status.removed => { R with score := upd R.score w (-1) }     -- Lines 8-10
        | Status.unset   =>
          -- Line 12: ζ_u = 0, then Lines 13-23 accumulate over rows above.
          let contribution :=
            processed.foldl (fun acc (xy : Row V) =>
              let x := xy.1
              let y := xy.2
              if w ∈ R.reps x then
                acc + max 0 (R.score y) + 1                             -- Line 17
              else if w ∈ R.reps y then
                acc + max 0 (R.score x) + 1                             -- Line 19
              else
                acc)                                                    -- Line 21: do nothing
              0
          { R with score := upd R.score w contribution }
      let R := scoreEndpoint u R
      let R := scoreEndpoint v R
      loop (processed ++ [(u, v)]) rest R
  loop [] R0.rows R0

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Algorithm 6 : FREEZE_AND_REMOVE(R, S, ψ, ω)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 6**. `psi`/`omega` model `ψ`/`ω` (`none` = the paper's
    `∅`). The Freeze Operation (Lines 1-5) is built directly from
    `TableState.freeze` (reused verbatim: it already performs "freeze ψ"
    + "delist ψ from every represents list", Lines 2 and 5), with only
    Line 4's "set L_ψ to null" added on top, since `TableState.freeze`'s
    blanket erase does not itself special-case ψ's own (now-irrelevant)
    list. The Remove Operation (Lines 6-15) genuinely generalizes
    `TableState.remove` (which freezes ω's represents-neighbours in one
    non-recursive step, cf. `remove_initialState_freezes_neighbors` in
    `reptable_ops_properties.lean`) into the paper's fully
    recursive cascade, so it is transcribed directly rather than reused
    as a black box. -/
public partial def freezeAndRemove (R : RTable G) (S : Finset V)
    (psi omega : Option V) : RTable G × Finset V :=
  -- Freeze Operation of Represents Table (Lines 1-5).
  let (R, S) :=
    match psi with
    | none    => (R, S)
    | some ψ  =>
      let ts := R.toTableState.freeze ψ                                -- Lines 2, 5 (reused)
      let ts := { ts with reps := upd ts.reps ψ (∅ : Finset V) }        -- Line 4
      let R := { R with toTableState := ts }
      let S := insert ψ S                                               -- Line 3
      (R, S)
  -- Remove Operation of Represents Table (Lines 6-15).
  match omega with
  | none    => (R, S)
  | some ω  =>
    let R := { R with status := upd R.status ω Status.removed }         -- Line 7
    let S := S.erase ω                                                  -- Line 8
    -- Lines 9-11: "for each non-frozen and unremoved endpoint u in R such
    -- that ω ∈ L_u do FREEZE_AND_REMOVE(R, S, u, ∅)".
    let candidates1 :=
      (Finset.univ.filter
        (fun u => R.status u = Status.unset ∧ ω ∈ R.reps u)).toList
    let (R, S) :=
      candidates1.foldl
        (fun (RS : RTable G × Finset V) u => freezeAndRemove RS.1 RS.2 (some u) none)
        (R, S)
    -- Lines 12-14: "for each non-frozen and unremoved endpoint u in L_ω do
    -- FREEZE_AND_REMOVE(R, S, u, ∅)".
    let candidates2 := (R.reps ω).toList.filter (fun u => R.status u = Status.unset)
    let (R, S) :=
      candidates2.foldl
        (fun (RS : RTable G × Finset V) u => freezeAndRemove RS.1 RS.2 (some u) none)
        (R, S)
    let R := { R with reps := upd R.reps ω (∅ : Finset V) }             -- Line 15
    (R, S)

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Algorithm 5 : VERTEX_ELIMINATION(R, S)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 5**. Lines 1-16: bottom-up pass over the rows (hence
    `R0.rows.reverse`). Both mirror-image sub-cases of Line 6 ("endpoint
    u in row remains and endpoint v in row is frozen") are handled, since
    the paper's `u`, `v` names within a row are otherwise arbitrary. -/
public partial def vertexElimination (R0 : RTable G) (S0 : Finset V) :
    RTable G × Finset V :=
  let rec loop (rows : List (Row V)) (R : RTable G) (S : Finset V) :
      RTable G × Finset V :=
    match rows with
    | [] => (R, S)                                        -- Line 16 (end); Line 17 returns this
    | (u, v) :: rest  =>
      let R := computeRepresentationScore R                            -- Line 3 (Algorithm 4)
      let su := R.status u
      let sv := R.status v
      let (R, S) :=
        if (su ≠ Status.unset) ∧ (sv ≠ Status.unset) then
          (R, S)                                                       -- Lines 4-5: continue
        else if su = Status.unset ∧ sv = Status.frozen then
          freezeAndRemove R S none (some u)                            -- Line 6-7
        else if sv = Status.unset ∧ su = Status.frozen then
          freezeAndRemove R S none (some v)                            -- labeling of Line 6-7
        else
          -- Line 9: both u, v neither frozen nor removed, represent only
          -- each other.
          if R.score u ≥ R.score v then
            freezeAndRemove R S (some u) (some v)                      -- Line 10-11
          else
            freezeAndRemove R S (some v) (some u)                      -- Line 12-13
      loop rest R S
  loop R0.rows.reverse R0 S0

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Algorithm 8 : DUADIC_HOP(R, S, ψ, ω, λ)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 8**. `psi`/`omega` model `ψ`/`ω` (`none` = `∅`), `lam`
    models `λ` as a `Finset V` of visited endpoints (matching the
    vocabulary of `IsDuad`/`DiminishingHop` in `thm6.lean`,
    which likewise use `Finset V`/`RepTable`). Per Line 1, exactly one of
    `ψ`, `ω` is `≠ ∅` on any genuine call; this is documented, not
    additionally enforced as a checked precondition, exactly as the
    paper's own comment is documentation rather than an assertion. -/
public partial def duadicHop (R : RTable G) (S : Finset V)
    (psi omega : Option V) (lam : Finset V) : RTable G × Finset V × Finset V :=
  -- Line 2: if ω ≠ ∅
  let (R, S, lam) :=
    match omega with
    | none   => (R, S, lam)
    | some ω =>
      if ω ∈ lam then
        (R, S, lam)                                          -- Lines 3-5: already visited, return
      else
        let lam := insert ω lam                                        -- Line 6
        let R := { R with status := upd R.status ω Status.removed }    -- Line 7
        let S := S.erase ω                                             -- Line 8
        -- Line 9: Q = ∅ (a queue of endpoints to be frozen); a `List V`
        -- appended at the tail preserves enqueue order (Lines 10-25).
        let step (u : V) (acc : Finset V × List V) : Finset V × List V :=
          let (lam, Q) := acc
          if u ∈ lam then
            (lam, Q)                                                   -- Line 11 fails: skip
          else
            let lam := insert u lam                                    -- Line 12
            if u ∈ S then (lam, Q) else (lam, Q ++ [u])                -- Lines 13-15
        -- Lines 10-17: "for each endpoint u in L_ω do ...".
        let (lam, Q) := (R.reps ω).toList.foldl (fun acc u => step u acc) (lam, [])
        -- Lines 18-25: "for each endpoint u in R such that ω ∈ L_u do ...".
        let candidates :=
          (Finset.univ.filter (fun u => ω ∈ R.reps u)).toList
        let (lam, Q) := candidates.foldl (fun acc u => step u acc) (lam, Q)
        -- Lines 26-29: "for each endpoint u in Q do
        --   Q = Q \ {u}; R, S, λ = DUADIC_HOP(R, S, u, ∅, λ)".
        let (R, S, lam) :=
          Q.foldl
            (fun (RSl : RTable G × Finset V × Finset V) u =>
              duadicHop RSl.1 RSl.2.1 (some u) none RSl.2.2)
            (R, S, lam)
        (R, S, lam)
  -- Line 32: if ψ ≠ ∅
  match psi with
  | none    => (R, S, lam)                                             -- Line 41
  | some ψ  =>
    let R := { R with status := upd R.status ψ Status.frozen }         -- Line 33
    let S := insert ψ S                                                -- Line 34
    -- Line 36: u = the other endpoint in ψ's row.
    match R.rows.find? (fun rc => rc.1 = ψ ∨ rc.2 = ψ) with
    | none => (R, S, lam)                                     -- (ψ not tabled: nothing to do)
    | some (a, b)   =>
      let u := if a = ψ then b else a
      if u ∈ S then
        duadicHop R S none (some u) lam                                -- Line 38
      else
        (R, S, lam)                                        -- Line 39 end; Line 41 returns this

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Algorithm 7 : DIMINISHING_HOPS(R, S)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 7**. Lines 2-3 initialize `R_diminished`, `S_diminished`
    (we also track `λ_diminished` and we start it at `∅`,
    exactly as `λ` itself is on Line 1). The inner "for each endpoint u in
    row" of Lines 11-18 restarts fresh from `R_original`/`S_original`/
    `λ_original` on each of its two iterations (Lines 19-21 reset them at
    the end of each pass, i.e. logically before the next), which we
    capture by calling `duadicHop` fresh from the saved original state
    each time. -/
public partial def diminishingHops (R0 : RTable G) (S0 : Finset V) : RTable G × Finset V :=
  let rec go (rows : List (Row V)) (Rd : RTable G) (Sd : Finset V) (lamd : Finset V) :
      RTable G × Finset V :=
    match rows with
    | [] => (Rd, Sd)                                      -- Line 27 (end); Line 28 returns (R, S)
    | (u, v) :: rest  =>
      let Roriginal := Rd; let Soriginal := Sd; let lamOriginal := lamd -- Lines 6-8
      if Rd.status u = Status.frozen ∧ Rd.status v = Status.frozen then -- Line 10
        -- Lines 11-18: "for each endpoint u in row do DUADIC_HOP(...);
        -- if |S| < |S_diminished| then update; [Lines 19-21 restore]".
        let tryEndpoint (w : V) (Rd Sd lamd : _) : RTable G × Finset V × Finset V :=
          let (R1, S1, l1) := duadicHop Roriginal Soriginal none (some w) lamOriginal  -- Line 12
          if S1.card < Sd.card then (R1, S1, l1) else (Rd, Sd, lamd)     -- Lines 14-18
        let (Rd, Sd, lamd) := tryEndpoint u Rd Sd lamd
        let (Rd, Sd, lamd) := tryEndpoint v Rd Sd lamd
        go rest Rd Sd lamd                                         -- Lines 23-26: R=S=λ=diminished
      else
        go rest Rd Sd lamd
  go R0.rows R0 S0 (∅ : Finset V)

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. Algorithm 3 : DIMINISHING_HOP_PHASE(R)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 3**. `m` (Line 6, `⌈m/2⌉`-many rounds) is read off as the
    number of rows already inserted into `R` by Algorithm 2 (one row per
    matching edge, Definition 14), i.e. `R0.rows.length`. -/
public partial abbrev diminishingHopPhase (R0 : RTable G) : Finset V :=
  let S0 : Finset V := ∅                                                -- Line 1
  let R1 : RTable G := { R0 with score := fun _ => negInf }              -- Lines 2-3
  let R2 := computeRepresentationScore R1                                -- Line 4 (Algorithm 4)
  let (R3, S3) := vertexElimination R2 S0                                -- Line 5 (Algorithm 5)
  let m := R0.rows.length
  -- Lines 6-8: "for each integer a in [1, m/2] do
  --   R, S = DIMINISHING_HOPS(R, S)".
  let rec repeatHops (n : ℕ) (R : RTable G) (S : Finset V) : RTable G × Finset V :=
    match n with
    | 0      => (R, S)
    | n + 1  => let (R', S') := diminishingHops R S; repeatHops n R' S'
  let (_, Sfinal) := repeatHops (m / 2) R3 S3
  Sfinal                                                                 -- Line 9

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. Algorithm 1 : VERTEX_COVER(G, k)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 1**, the top-level decision procedure. `M` is a perfect
    matching given as its total involutive partner function (§2' above);
    `Vs` is Line 1's lexicographically sorted vertex list; `adj0` is `G`'s
    adjacency-list function, needed by Algorithm 2's BFS. Since `M` is a
    perfect matching, `{ (v, M v) : v ∈ Vs, v <lex M v }` enumerates each
    matching edge exactly once (Line 3). -/
public abbrev vertexCover
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool)
    (k : ℕ) : Bool :=
  -- Line 1: Vs (already supplied as an argument, per the design note above).
  -- PHASE I (Lines 2-6).
  let matchingEdges : List (Row V) :=
    Vs.filterMap (fun u => if lt u (M u) then some (u, M u) else none)   -- Line 3
  if k < matchingEdges.length then
    false                                                                -- Lines 4-5
  else
    let inM : V → V → Bool := fun a b => decide (M a = b ∨ M b = a)
    -- PHASE II (Lines 7-8).
    let R := populateRepresentsTable (G := G) adj0 inM Vs                -- Line 8 (Algorithm 2)
    -- PHASE III (Lines 9-10).
    let S := diminishingHopPhase R                                      -- Line 10 (Algorithm 3)
    -- Lines 11-14.
    decide (S.card ≤ k)

end

-- ═══════════════════════════════════════════════════════════════════════════
-- §10. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  This file defines executable `partial def`s only.

  Reuse map (what came from where):
    • `Status`, `RepList`, `TableState`, `initialState`, `TableState.freeze`
        — `reptable_ops_properties.lean` (imported transitively).
    • `RepTable` (`M`, `isPM`, `row`, `row_pair`)
        — `lemma4.lean` (imported transitively); target type of
          `RTable.toRepTable`.
    • `VCover`, `MinVCover`
        — `thm6.lean` (imported
          transitively); not used by the executable code itself (no new
          correctness theorem is attempted here) but available for a
          follow-on statement relating `vertexCover`'s Boolean output to
          `MinVCover`, exactly the kind of statement `Theorem4`/
          `Theorem6`/`Theorem7` already prove about the *result* of running
          these algorithms.
    • `FrozenSet`, `IsValidFreezeRemove`
        — `thm4.lean` (imported transitively); likewise available
          but unused, since `FrozenSet st = {v | st.status v = frozen}` is
          definitionally what `Finset.filter (status = frozen) univ`
          would recompute from any `RTable`'s `.status` field.
    • `IsDuad`, `DiminishingHop`
        — `thm6.lean` (imported transitively); these are exactly
          the *specification* Algorithms 7/8 are meant to implement (a
          `DuadicHop`/`DiminishingHop` packages a duad plus a resulting
          valid state, which is precisely what `duadicHop`/`diminishingHops`
          compute) — again, connecting the two is a natural follow-on, not
          attempted here since it is a new theorem, not part of "formalize
          the algorithms as is".

  Line numbers in comments refer to the pseudocode boxes on pp.52-57
  (Algorithms 1-8).
-/
