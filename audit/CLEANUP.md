# Repository cleanup

This revision keeps current proof and reproduction inputs. Git is the archive
for obsolete campaign logs, reviews and frozen releases.

## Removed

Counts are cumulative from the merged resource-proof commit `0e38bf8`,
including the earlier artifact cleanup in PR #80 and this follow-up.

| Category | Files | Bytes |
| --- | ---: | ---: |
| `.cursor` | 3 | 1,134 |
| `.pr27-receipts` | 4 | 8 |
| `Lean campaigns / replaced receipt modules` | 77 | 2,766,298 |
| `audit/CAMPAIGN.md` | 1 | 10,855 |
| `audit/CLOUD_ORCHESTRATOR.md` | 1 | 2,265 |
| `audit/REMOTE-STATUS.md` | 1 | 24,733 |
| `audit/WAVE0.md` | 1 | 15,032 |
| `audit/history` | 4 | 203,336 |
| `audit/receipts` | 802 | 55,035,769 |
| `audit/release` | 7 | 135,711 |
| `audit/reviews` | 63 | 548,049 |

- `.pr27-receipts` contained four two-byte success status files with no current consumer.
- `.cursor` and the campaign orchestration documents described obsolete worker setup.
- Dated review/build logs, historical assumption/guarantee snapshots, candidate
  journals and frozen release manifests are superseded by the current source,
  metadata, clause map and `make check`.
- The standalone protocol slot/withdrawal extraction campaign, ordinary-block
  extensions and unused umbrella modules are outside the retained evidence
  dependency graph. Their tests passed at stage 3 before removal. The slot/withdrawal
  test was already included by the old recursive Lake glob; stage 2 made that
  coverage explicit, then this broader cleanup removed the unused campaign.
- 193 small candidate modules were consolidated into 47 topic modules at stage 3.
  Two resulting topics were later removed with their unused campaigns. These
  moves are separate from the deletion counts above.

The exact deleted paths and original contents can be inspected with:

```sh
git diff --name-status --diff-filter=D 0e38bf80ed60dbf3f0927312ebb598bb6f731895 HEAD
```

Stage 3's complete tested source is `8ef5bc2307843ef68df8e55fa3d9584d7f0a6b3b`.
The original resource proof is preserved at
`0e38bf80ed60dbf3f0927312ebb598bb6f731895`. The public site's immutable proof
snapshots continue to resolve through Git history.

## Kept because it is used

- The three registered guarantees, their six same-predicate refutations and
  `ResourceAssumptions` remain. The direct theorem statements and proof bodies
  are unchanged; only their support imports moved.
- Factory deployment and the checked deposit/exit SYSTEM block pair remain as
  current supporting evidence. Their resource/history and source-adapter
  dependencies remain in the candidate library. The retained small tests
  exercise those source adapters.
- The old model/CFG/Ξ campaign modules are removed. Their used execution
  helpers now live in `Execution/*`. `Tests.MutationReceipts` retains only the
  original fixture definitions and five native receipts; unused sibling tests,
  old universal parents and their abstract metadata are removed. Public names
  of the retained definitions and receipt statements are preserved.
- Seven source/provenance archives under `audit/receipts` supply pinned external
  source bodies, genesis data provenance and the factory-regression input.
  `resource-assumptions.json` records the merged resource proof's exact premises
  and historical validation; it does not certify this new revision.
- A-NATIVE-DECIDE remains because the five finite drain/control witnesses still
  depend on native evaluation. The correctness parents and funded LOG0 witness
  retain only standard Lean axioms.
- `scripts/gen_blocks.py` remains the generator for `Execution/Blocks.lean`;
  Lean checks the generated equations. Pins, lock data, deployment verification
  and optional Anvil regression scripts remain reproducible.

## Preventing drift

`audit/delivery-roots.json` names the retained evidence and regression roots.
The layout checker rejects modules outside their dependency closure and rejects
superseded-layer imports in the correctness core. `Audit.Trust` rejects new
correctness/refutation axioms; `Tests.ResourceAssumptions` protects the eight
resource theorems. The artifact checker rejects unreferenced receipts. CI runs
the complete `make check`.
