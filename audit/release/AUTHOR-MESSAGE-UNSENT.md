# Draft to authors — UNSENT, approval required before transmission

We have proved revised P-SUBMIT-1, P-DRAIN-1 and P-CONTROL-1 claims for the
Deposit/Exit bytes from ethereum/sys-asm
83f9801245ff56878a450b5625801101b9a225a1 under an explicit initialized-history
domain in EVMYulLean b62586650b4f96cc6da25f36574aaa8f329a6420.
This does not establish full Ethereum applicability. Original requested clauses,
precise assumptions and exact build/review receipts accompany the candidate.

Three reproducible issues need clarification:

1. The fee loop is not limited to256 iterations. With excess1608,count0 it
   takes257 iterations; at1620,count0 it takes258 and returns
   243056981773394081136356734028591621772929 wei, one wei above a256-term partial
   result. Actual bytecode agrees with the unbounded natural tariff at both
   inputs. Please confirm that any reference implementation must run to actual
   termination rather than use a256-step cutoff.
2. At numerator2893, actual Deposit and Exit getter output is
   32087365885911168062721653499988857431024628719292649881555161070975172167 wei;
   the natural algorithm returns
   80668064690921409049190791237320678716946849613533250306370202067869504081 wei.
   The word result is below the preceding2892 quote. Is the intended promise
   mathematical fake_exponential, exact ordered EVM word operations, or a
   protocol-enforced reachable domain? If the latter, which concrete admission,
   credit, upgrade and gas rules establish that domain? Intent alone will not
   establish economic or security harmlessness.
3. Nonempty SYSTEM sets INHIBITOR; a later empty SYSTEM resets it to0 and
   performs a normal drain. This is reversible for both bytecodes. If retirement
   is intended permanent, what exact restriction prevents subsequent empty
   SYSTEM calls or what upgrade replaces the runtime? Which fork stage owns
   that rule, and what happens to queued requests and excess on transition?

Reproduction: audit/receipts/direct-semantics-20260909.json and
scripts/check_direct_semantics.py (Anvil1.5.0/Prague injected state), together
with kernel-checked FeeSafeDomain/FeeBoundary and ReleaseInhibitionCycle.
These are not canonical reachability experiments. The separate reported
artificially funded3307-submission history has not been independently verified
in the included artifacts.

Please also identify the intended fork/version, exact deployment transactions,
SYSTEM call authorization/order/resources, and rules relevant to the old
scalar versus proposed dual gas/refund accounting and type4 delegation. We
will assess those against the actual theorem premises rather than assume the
pinned Lean semantics represents that protocol automatically.

No EIP amendment, policy adoption, publication or external transmission has
been made by this audit candidate.
