# Verified divergences and reproduction domains

Evidence: unchanged `scripts/check_direct_semantics.py` and
`audit/receipts/direct-semantics-20260909.json`, rehashed and independently
reviewed in `release-findings-review-20260910.json`. That receipt ran Anvil1.5.0,
Prague, with injected runtime/storage and SYSTEM impersonation. It is a finite
execution corroboration, not canonical reachability or an Amsterdam gas test.
The release reuses this valid unchanged evidence; it does not claim a fresh run.
Kernel proofs `FeeSafeDomain` and `FeeBoundary` are included in the release build.

To reproduce the finite cases with the recorded dependencies: `make direct-regressions`.
The script injects excess=numerator,count=0 and calls both pinned empty-data
getters. Exact artifacts/pins and every returned byte are in the receipt.

| Numerator | Word iterations | Actual word fee (wei) | Natural fee (wei) | Historical256 partial fee (wei) |
|---|---|---|---|---|
| 1608 | 257 | 119989470856188333158662703311252429458084 | 119989470856188333158662703311252429458084 | 119989470856188333158662703311252429458084 |
| 1620 | 258 | 243056981773394081136356734028591621772929 | 243056981773394081136356734028591621772929 | 243056981773394081136356734028591621772928 |
| 2892 | 462 | 76059800903738432429721259523001950250726052916847211303159755524395288041 | 76059800903738432429721259523001950250726052916847211303159755524395288041 | 76059800863616758702704020033436639992485407048739182564101426982217163231 |
| 2893 | 457 | 32087365885911168062721653499988857431024628719292649881555161070975172167 | 80668064690921409049190791237320678716946849613533250306370202067869504081 | 32087365885607572727530807860580823726471996586990252895353367470359807971 |

**1608.** A completed fee calculation takes257 iterations. A256-step completion
claim is false, even though the final quotient happens to match its256-step
partial value. This is a proof/model truncation defect. It does not establish
an incorrect bytecode charge or a security exploit.

**1620.** Completion takes258 iterations. The actual bytecode and unbounded
natural algorithm agree; the historical256 partial calculation is one wei
smaller. This refutes using that truncated model to certify admission/quotes.
A client relying on that partial quote could underpay and be rejected; this
receipt verifies the quote discrepancy, not that separate underpaid-append
transaction. There is no demonstrated natural/word divergence at1620.

**2893.** The exact operation-by-operation word recurrence diverges from the
natural algorithm and the word fee drops about57.8% from2892. The kernel proofs
`FeeBoundary.word_price_not_mathematical` and `.local_fee_drop` establish both
facts; injected calls to both runtimes return the word value above. All inputs
≤2892, including intermediate products/sums, satisfy the proved agreement
domain. Adding a modulo only to the final natural formula would not describe
the bytecode and is not the proof used here.

Functionally, unrestricted mathematical tariff agreement and global word-fee
monotonicity are false. Economically, the drop changes the intended congestion
price outside the certified domain. The absolute price remains enormous; this
alone does not prove harmlessness. Security impact depends on a real path to
that state and available funds. No canonical exploit, loss bound or assurance
of harmlessness is claimed. The release's explicit finite-history credit
domain *derives* exclusion of enabled numerator2893; it is not a proof that
Ethereum satisfies that domain.

**Inhibition cycles.** `ReleaseInhibitionCycle.after_history` constructs, for
either runtime after the scoped exact initialized history, an actual nonempty
SYSTEM call followed by an actual empty SYSTEM call. Both succeed with the
specified30M scalar gas/fuel≥8503; slot0 becomes INHIBITOR then0, count becomes0
on both calls, and the three guarantees and next invariants hold. Both calls
also perform the normal FIFO drain. Repeating suitable SYSTEM edges is allowed
by the history relation; no permanent-retirement policy is assumed. The older
finite Anvil receipt specifically corroborates Exit user rejection while
inhibited and an empty SYSTEM unlock, not a full cycle for both variants.

A permanence promise is false for these bytes without a restriction on later
SYSTEM inputs or replacement code. Functionally, empty SYSTEM re-enables users.
Economically, it resets excess and therefore can reset future quotes. Security
impact concerns the authority and scheduling of SYSTEM and whether retirement
was intended to be irreversible. An author statement of intent cannot resolve
these effects or establish innocuity; a policy decision remains unadopted.

**Other checked boundaries.** The finite receipt records intermediate
SYSTEM-addition overflow in injected states, so unrestricted natural fold
reasoning is invalid there; safe-history invariants justify the natural fold
inside this release. It also records an inner successful Exit append followed
by ancestor REVERT: storage, balances and final logs roll back while gas is
paid. Executed marked LOG0 occurrences used for resource bounds are distinct
from the retained occurrence list that determines persistent records/logs.

**Report-only claims kept separate.** The GPT Pro report at the preserved
`inputs/eip8282-review.txt` copy (SHA256
`09ae6b6c5d529839480ec5a947a64628398d6ae3a81647e7db5f0b1225828bf6`)
also describes3307 submissions/207 groups from constructor with artificial
funding. No matching chain artifact was found in the current evidence and that
experiment was not rerun. It is not included as verified reachability.
Even a verified artificially funded construction would remain distinct from
canonical Ethereum reachability. The same caution applies to its separate
underpaid-append experiment. The supplied report is evidence to investigate,
not an axiom or an automatically established result.
