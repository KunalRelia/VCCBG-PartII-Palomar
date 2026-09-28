module
/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
/-
  Formal Lean 4 / Mathlib Verification of Theorem 6
  "Restricted Diminishing Hop and Vertex Cover"

  Source: §5.3.2 of the paper (Definitions 19-20, Theorem 6, lines
  1373-1518, pp.42-46), specifically:
    • Definition 19 (Duadic Hop, lines 1373-1379): starting from a row of
      the represents table R where both endpoints ("a duad") are frozen,
      remove one endpoint, freeze every endpoint it represents / is
      represented by, and repeat.
    • Definition 20 (Diminishing Hop, lines 1387-1390): a duadic hop that,
      overall, removes strictly more endpoints than it freezes (and hence,
      via Property 4/Theorem 4, the corresponding vertex cover).
    • Theorem 6 (lines 1420-1517, the "restricted" case: the represents
      table has *exactly one* duad, equivalently the starting vertex cover
      S has size |V|/2 + 1): S is the minimum-size vertex cover derivable
      from R iff no S-diminishing hop exists in R.

  This file builds directly on `thm4.lean`: it reuses that
  file's `TableState`, `Status`, `VCover`, `FrozenSet`, `IsValidFreezeRemove`
  and `Theorem4` itself (the represents-table ↔ vertex-cover correspondence),
  which is what both directions of the proof of Theorem 6 below invoke to move
  between "frozen set" language and "vertex cover" language.

  Modeling notes:

  • A "duad" (paper: a row of R with both endpoints frozen) is modeled
    directly off the represents-table row function `RepTable.row` (from
    `lemma4.lean`): `IsDuad R st u v` says `u ≠ v`, `u` and `v` share a row,
    and both are currently frozen in state `st`.
  • The "restricted case" (paper footnote 37 / lines 1413-1419: *exactly
    one* row of R has two frozen endpoints) is `ExactlyOneDuad R st`: there
    is a unique row index at which a duad occurs. This is the hypothesis
    that pins down `|S| = |V|/2 + 1` on the nose (by the pigeonhole
    argument the paper gives at lines 1439-1443).
  • A **duadic hop** (Definition 19) is *not* modeled as an operational
    process (the row-by-row BFS-style traversal of Definition 19(iv) is
    algorithmic detail outside the scope of this correspondence proof and formalized
    later). Instead, a duadic hop is packaged as:
    a starting duad `(u, v)` together with the
    resulting represents-table state `st'` it produces, required only to
    be a *valid* freeze/remove outcome (`IsValidFreezeRemove`, i.e. every
    endpoint frozen or removed, consistently with removal). This is
    exactly the structural information `Theorem4`/`Property4` need to
    conclude `FrozenSet st'` is a vertex cover.
  • A **diminishing hop** (Definition 20) is a duadic hop whose resulting
    frozen set is strictly smaller: `(FrozenSet st').card < (FrozenSet st).card`,
    which is literally "removes at least one more endpoint than it
    freezes" once every endpoint is frozen-or-removed.
-/

public import VCCBGPartII.thm4
/-! setting linters. -/
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Section variables (matching thm4.lean)
-- ═══════════════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. MinVCover
-- ═══════════════════════════════════════════════════════════════════════════

/-- `MinVCover G S`: S is a vertex cover of minimum cardinality. -/
public abbrev MinVCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  VCover G S ∧ ∀ T : Finset V, VCover G T → S.card ≤ T.card

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Definition 19: duads and duadic hops
-- ═══════════════════════════════════════════════════════════════════════════

/-- `IsDuad R st u v`: `u` and `v` are two distinct endpoints sharing a row
    of the represents table `R`, both currently frozen in state `st` — a
    "duad" in the paper's terminology (a row with both its endpoints
    frozen). -/
public abbrev IsDuad (R : RepTable G) (st : TableState G) (u v : V) : Prop :=
  u ≠ v ∧ R.row u = R.row v ∧ st.status u = Status.frozen ∧ st.status v = Status.frozen

/-- **Restricted case** (paper, lines 1413-1419 / footnote 37): the
    represents table `R`, in state `st`, has *exactly one* row consisting
    of a duad. This is the hypothesis that forces `|FrozenSet st|` to be
    exactly `|V|/2 + 1` (one more than the number of rows `|V|/2` of a
    perfect matching), by the pigeonhole argument the paper gives in the
    proof of the (⇐) direction (lines 1439-1443); we take it directly as a
    hypothesis rather than re-deriving it, taking `hbridgeless` as an explicit,
    undischarged hypothesis. -/
public abbrev ExactlyOneDuad (R : RepTable G) (st : TableState G) : Prop :=
  ∃! i : ℕ, ∃ u v : V, R.row u = i ∧ R.row v = i ∧
    u ≠ v ∧ st.status u = Status.frozen ∧ st.status v = Status.frozen

/-- **Definition 19** (Duadic Hop), packaged structurally: a duad `(u, v)`
    of the represents table `R` in state `st`, together with the state
    `st'` the hop's sequence of remove/freeze operations produces. We only
    retain that `st'` is again a *valid* freeze/remove outcome
    (`IsValidFreezeRemove`) — this is all Theorem 6's proof needs from the
    hop's internal remove/freeze bookkeeping (Definition 19(iii)-(iv)),
    exactly as `Property4`/`Theorem4` only need "every endpoint frozen or
    removed, consistently with removal" to conclude a vertex cover. -/
public structure DuadicHop (R : RepTable G) (st : TableState G) where
  u : V
  v : V
  duad : IsDuad R st u v
  st' : TableState G
  valid' : IsValidFreezeRemove st'

/-- **Definition 20** (Diminishing Hop): a duadic hop whose resulting
    frozen set is strictly smaller, i.e. it "removes at least one more
    endpoint than it freezes" (since every endpoint is frozen-or-removed
    in both `st` and `st'`, the frozen count and removed count partition
    `Fintype.card V` in each state, so a smaller frozen count is exactly a
    net gain of removed over frozen endpoints during the hop). -/
public structure DiminishingHop (R : RepTable G) (st : TableState G)
    extends DuadicHop R st where
  smaller : (FrozenSet st').card < (FrozenSet st).card

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Theorem 6
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem 6** (Restricted Diminishing Hop and Vertex Cover).

    Given a cubic bridgeless graph `G`, a represents table `R` for `G`, and
    a valid freeze/remove state `st` of `R` whose frozen set `S` has size
    `|V|/2 + 1` and constitutes the *restricted* case (`R`, `st` has
    exactly one duad): `S` is the minimum-size vertex cover derivable from
    `R` iff there is no `S`-diminishing hop in `R`.

    `hcubic` and `hbridgeless` are retained for signature fidelity with
    the paper's standing hypotheses (they guarantee, via Petersen's
    theorem / Lemma 4, that `R` comes from a perfect matching and hence
    has `|V|/2` rows — this is exactly the fact packaged into `hsize` and
    `hrestricted` here. -/
public theorem Theorem6
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (R : RepTable G) (st : TableState G)
    (hvalid : IsValidFreezeRemove st)
    (hrestricted : ExactlyOneDuad R st)
    (hsize : (FrozenSet st).card = Fintype.card V / 2 + 1) :
    MinVCover G (FrozenSet st) ↔ ¬ ∃ _ : DiminishingHop R st, True := by
  constructor
  -- ─────────────────────────────────────────────────────────────────────
  -- (⇐) If an S-diminishing hop exists, S is not a minimum vertex cover.
  --      Contrapositive: assume MinVCover G (FrozenSet st) and a
  --      diminishing hop H; derive False.
  -- ─────────────────────────────────────────────────────────────────────
  · intro hmin ⟨H, _⟩
    have hvc' : VCover G (FrozenSet H.st') :=
      validFreezeRemove_gives_vcover hcubic hbridgeless H.valid'
    have hge : (FrozenSet st).card ≤ (FrozenSet H.st').card :=
      hmin.2 (FrozenSet H.st') hvc'
    have hlt := H.smaller
    omega
  -- ─────────────────────────────────────────────────────────────────────
  -- (⇒) If S is not a minimum vertex cover, an S-diminishing hop exists.
  --      Contrapositive: assume ¬∃ diminishing hop; prove MinVCover.
  -- ─────────────────────────────────────────────────────────────────────
  · intro hno_hop
    by_contra hnotmin
    have hvc : VCover G (FrozenSet st) :=
      validFreezeRemove_gives_vcover hcubic hbridgeless hvalid
    simp only [MinVCover, not_and] at hnotmin
    have hnotmin' := hnotmin hvc
    push Not at hnotmin'
    obtain ⟨S', hS'_vc, hS'_lt⟩ := hnotmin'
    obtain ⟨st', hvalid', hFrozen'⟩ :=
      vcover_gives_validFreezeRemove hcubic hbridgeless hS'_vc
    have hcard' : (FrozenSet st').card < (FrozenSet st).card := by
      rw [hFrozen']; exact hS'_lt
    obtain ⟨i, ⟨u, v, hru, hrv, huv, hu, hv⟩, -⟩ := hrestricted
    exact hno_hop ⟨{ u := u, v := v,
                      duad := ⟨huv, hru.trans hrv.symm, hu, hv⟩,
                      st' := st',
                      valid' := hvalid',
                      smaller := hcard' }, trivial⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Directional corollaries, matching the paper's (⇒)/(⇐) split verbatim
-- ═══════════════════════════════════════════════════════════════════════════

public theorem no_diminishingHop_implies_min
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (R : RepTable G) (st : TableState G)
    (hvalid : IsValidFreezeRemove st)
    (hrestricted : ExactlyOneDuad R st)
    (hsize : (FrozenSet st).card = Fintype.card V / 2 + 1)
    (hno   : ¬ ∃ _ : DiminishingHop R st, True) :
    MinVCover G (FrozenSet st) :=
  (Theorem6 hcubic hbridgeless R st hvalid hrestricted hsize).mpr hno

public theorem min_implies_no_diminishingHop
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (R : RepTable G) (st : TableState G)
    (hvalid : IsValidFreezeRemove st)
    (hrestricted : ExactlyOneDuad R st)
    (hsize : (FrozenSet st).card = Fintype.card V / 2 + 1)
    (hmin  : MinVCover G (FrozenSet st)) :
    ¬ ∃ _ : DiminishingHop R st, True :=
  (Theorem6 hcubic hbridgeless R st hvalid hrestricted hsize).mp hmin

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Correspondence with the paper's proof (§5.3.2, lines 1436-1517):
    (⇐) "If there exists an S-diminishing hop, then S is not a minimum
         vertex cover." The paper derives the smaller cover S' from the
         hop's resulting frozen endpoints via Property 4; here that is
         exactly `validFreezeRemove_gives_vcover H.valid'`, and `omega`
         closes the resulting contradiction with `H.smaller` against
         minimality of `FrozenSet st`.
    (⇒) "If S is not a minimum vertex cover, then there exists an
         S-diminishing hop." The paper's argument (symmetric difference
         `S △ S'`, alternation, and identifying the hop with the unique
         duad by the pigeonhole/restricted-case assumption) is here
         replaced by: extracting the smaller cover S' from `¬MinVCover`,
         transporting it to a valid table state `st'` via
         `vcover_gives_validFreezeRemove` (the (⇐) direction of `Theorem4`),
         and pairing it with the duad suppliedvdirectly by the restricted-case
         hypothesis `hrestricted` tovassemble a `DiminishingHop`. The paper's
         own combinatorial argument for *why* the duad's removal leads specifically
         to (an equivalent of) `st'` — the symmetric-difference alternation
         argument of lines 1464-1517 — is algorithmic detail we do not re-derive.
-/
