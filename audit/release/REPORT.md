# EIP-8282 scoped audit release candidate

The revised guarantees are complete conditional bytecode theorems for **both
Deposit and Exit** in the pinned EVMYulLean semantics. On the explicit
initialized-history domain, the same actual call receipt establishes authentic
paid admission/one record/one LOG0 (P-SUBMIT-1), exact capped FIFO output and
pointers with no user drain (P-DRAIN-1), and mathematical fee/count/excess/
inhibition control (P-CONTROL-1), including relevant message rollback.
The verification status and exact candidate commit are resolved by MANIFEST.json.
Canonical Ethereum satisfaction of this domain remains unproved.

The primary API is `ReleaseCandidate.composed`: all three observations at the
next call, plus exact committed queue/log effects and all nested local
guarantees for every indexed transaction in the same actual history. The
complete call tree distinguishes executed work, retained effects and ancestor
rollback. `ReleaseCandidate.call` is the simpler next-call projection.

During this hour the proof interfaces became stronger:

- Exact factory initialization and actual history now supply installed code,
  both queue/control invariants, the structural work bound and enabled natural
  fee numerator≤2892. Those are no longer premises of the public call API.
- Successful getters and funded paid submissions are constructed from input
  shape, enabling conditions and stated resources; quote termination, storage
  fit and a convenient transferred-value ceiling are derived. Submission also
  establishes its next invariant. No desired success/postcondition is assumed.
- Both bytecodes have a proved actual SYSTEM latch→unlock cycle, composed with
  the same history and all three guarantees.
- Computed checked terminal/EOF outcomes connect to those guarantees with
  initial owner derived. This adapter uses synthetic replay resources and is
  deliberately not a full Ethereum account-world/gas equivalence theorem.

Read [CLAIMS.md](CLAIMS.md) for precise revised statements,
[ORIGINAL-GUARANTEES.md](ORIGINAL-GUARANTEES.md) for the original request,
[CLAUSE-MAP.md](CLAUSE-MAP.md) for clause→theorem→domain→commit,
and [PREMISES.json](PREMISES.json) for every transitive premise, consumer,
derivation, remaining dependency and owner. This is evidence attached to the
existing structured task ledger, not a second roadmap.

The domain restricts *inputs*: actual linked deployments and finite pinned
semantic histories, explicit old transaction admission and computation fuel,
a same-total bounded credit ledger, and distinct64-bit block slots whose
old receipt charges fit block limits. These yield arithmetic and physical
queue safety; no noWrap/TAIL cap, desired poststate, convenient wealth ceiling
or assumed fee termination is inserted. These input restrictions are not
claimed to be Ethereum rules. Upgrades are outside this domain.

The operational tariff follows every word operation in order and admits
arbitrary finite completed executions. The natural tariff agreement domain is
≤2892, derived on enabled states in this history. There is no256-iteration
ceiling.462 is a sufficient witness on the safe interval, not a semantic
cutoff. Safety is separate from termination and resource sufficiency. The
stated gas bounds apply to the pinned scalar model; replay gas and actual
source gas remain separate quantities.

[Findings](FINDINGS.md) distinguish1608 (completion exceeds256),1620 (the
truncated model underquotes by1wei),2893 (real word/natural divergence and
fee drop), and reversible inhibition. Each includes functional, economic and
security implications and its reproduction domain. Finite injected receipts
are reused only after source/pin hash validation. The reported artificially
funded chain is not silently promoted to a verified or canonical history.

The remaining trust boundary is explicit: Lean kernel and standard axioms (`propext`, `Classical.choice`, `Quot.sound`),
the pinned interpreter definitions as the subject semantics, exact artifact
bindings and deployment hash/collision inputs, and faithful source projections
where used. No new project/native axiom supports the universal claims. Five
historical finite mutant execution witnesses retain disclosed native receipts;
that is test evidence, not a universal correctness assumption.

Ethereum application still needs full source account/code/transient/journal
and occurrence correspondence, actual dual gas/refund/admission/delegation,
canonical genesis/deployment/credit/withdrawal producers, and approved SYSTEM,
inhibition and upgrade policy. Known old/source differences are concrete, so
no blanket interpreter-equivalence assumption is advertised. BLS validation
and consensus processing beyond these three claims are outside scope; this
does not excuse the EL/SYSTEM obligations needed for Ethereum application.
No proposed protocol variant is adopted or counted as closed.

The [author message](AUTHOR-MESSAGE-UNSENT.md) remains unsent. No publication,
merge, EIP amendment or normative adoption was performed. Unverified account
lookup/dispatch drafts remain outside the candidate. Exact compilation,
axiom, mutation and independent review receipts are linked by the manifest;
unavailable or unfinished checks are not marked passed.
