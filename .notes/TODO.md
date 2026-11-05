# Ideas considered but not scheduled

Designs that were worked out far enough to be worth keeping, and then deliberately not started.
Neither a gap nor a plan: [MISSING.md](MISSING.md) tracks the API-surface gap against lean-cvc5,
and `CLAUDE.md`'s "What is left" tracks the work that *is* queued.

## A SQL API over relations and tables

Relations and tables are the relational algebra, so SQL is an encoding away — but it is an encoding
every user would otherwise write themselves. The mapping is already complete:

| SQL | today |
|---|---|
| `FROM a, b` | `tableProduct` |
| `JOIN … ON` | `tableJoin`, on an interleaved `Array (Nat × Nat)` |
| `WHERE` | `tableFilter` plus a hand-built lambda |
| `SELECT cols` | `tableProject` — typed, see below |
| `SELECT DISTINCT` | `tableSetof` |
| `GROUP BY` | `tableGroup` / `tableAggregate` |
| `UNION ALL` / `UNION` | `tableUnionDisjoint` / `setof` after `tableUnionMax` |
| `INTERSECT ALL` / `EXCEPT ALL` | `tableInterMin` / `tableDifferenceSubtract` |
| `COUNT(*)` | `tableCard` |
| `EXISTS` / `IN` | `tableSome` / `tableMember` |

What a user supplies by hand is every predicate and fold, as a lambda assembled from `BVar.mk` and
the tuple accessors. Removing that is what is left of the point; column positions were the other
half and are now typed.

**The typed column machinery has landed** — it was the centrepiece here, but projection is
relational algebra rather than SQL, so it went in on its own merits. `ColHead`/`Col`/`Cols` and the
`col%`/`cols%` notation are in [Types/Relation.lean](../Cvc/Types/Relation.lean), with `Term.tupAt`,
`tupProject`, `relProject` and `tableProject` over them. So a SQL layer would start from `SELECT`
already being typed:

```lean
def Sql.project (cols : Cols α β α' β') (t : Term (Tab α β)) : Env (Term (Tab α' β')) := …
```

Three encodings were prototyped before committing, and the losing ones are worth not retrying:

| | call site, columns 2 then 0 | inferred type | position 4 of 4 |
|---|---|---|---|
| structural witness | `.cons (.next (.next .here)) (.last .here)` | `Tab [String] Int` | rejected |
| `Fin` + computed type | `.cons 2 (.last 0)` | `Tab [compAt … ↑2] (compAt … ↑0)` | **wraps to 0** |
| numeral macro (chosen) | `cols% [2, 0]` | `Tab [String] Int` | rejected |

The middle row is the one to remember. `Fin`'s `OfNat` reduces modulo the bound, so an out-of-range
literal is silently reinterpreted rather than refused — `.last 4` on a four-component tuple
elaborates, at column *zero*. It also displays every derived index as an unreduced `compAt`
application, which a pipeline of projections and joins would carry through every goal and error
message, and it needs `@[expose]` to compile across modules at all.

What the chosen form gives up is error *wording*: an out-of-range position reports a mismatch on
the macro-expanded `Col.zero.next`, not "position 4 out of range for a 4-component tuple". A custom
elaborator in place of the macro would fix that, and is worth doing only if it proves confusing in
practice.

The `ON` clause is the same idea over two tables, and buys a check cvc5 currently makes at run
time: `On.cons (l : Col α β γ) (r : Col α' β' γ)` shares one `γ`, so joining columns of different
types stops compiling. It still flattens to the interleaved array, so the odd-length mistake stays
unrepresentable.

`WHERE` is the clean case for a **HOAS surface** — the wrapper mints the row variable and builds
the lambda, so the row cannot escape its predicate:

```lean
def Sql.restrict (p : BVar (Tup α β) → Env (Term Bool)) (t : Term (Tab α β))
  : Env (Term (Tab α β))
```

Three things found while designing it, each of which would otherwise be found the hard way:

- **`tableAggregate` loses the group key.** Its answer is one accumulator per group, so
  `GROUP BY dept SELECT dept, SUM(pay)` cannot come back as pairs unless the fold puts the key
  there itself — accumulate a `Tup [Dept] Int`, have each step copy the key column (idempotent,
  a group agreeing on it) and start from a dummy. It works, it is ugly, and the API should do it
  once rather than each user rediscovering it.
- **SQL `NULL` is `Option`, and the nullable lifts are already right — except for the
  connectives.** `NULL + 1 = NULL` and `NULL < 3 = NULL` are exactly what `add?`/`lt?` do, and
  `NULL = NULL` being unknown is `equal?`'s documented trap turned into a specification. But SQL's
  `AND`/`OR` are *not* strict: `FALSE AND NULL` is `FALSE` where `and?` gives `NULL`. So the SQL
  layer needs its own three-valued connectives and must not reach for the lifts, and `WHERE` needs
  an explicit "unknown counts as false" step. Both want verifying against cvc5 before being
  committed to.

Schema constraints read as assertions: `notNull` via `tableAll` over `isSome`; a primary key
plausibly as "the distinct key projection has the same cardinality as the table"; a foreign key as
a `tableSubtable` between `setof`-ed projections. Those last two are sketches, unverified, and are
the least trustworthy part of this.

`On` carries no terms, so it would join `Col`/`Cols` in `Types/Relation.lean`, with
`{Untyped,Typed}/Sql.lean` above them. Sort-erased the layer is thin — positions are already
`Nat`s — so the value is nearly all typed, the same split relations and tables have. Bags first,
SQL keeping duplicates; `Rel` variants only where they cost nothing. Note `where` and `from` are
Lean keywords, so the names have to be `restrict`/`project` or similar.

In dependency order, with the column machinery already done: `On` and a typed `join`; then
`restrict` and the set operators, with SQL's `ALL`/`DISTINCT` distinction spelled out in the names;
then aggregates; then NULL semantics and schema constraints. A `sql!` DSL would
come last and is hard to justify before the rest has been used on something real.

The use case that would justify the whole thing is **query equivalence** — assert the schema
constraints, build two queries, assert they differ, expect `unsat`. Worth writing that test first,
since it exercises projection, join, restriction and the set operators at once.
