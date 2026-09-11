# Getter-scope erratum to the direct parent packaging review

9 September 2026. This note corrects `/tmp/eip-direct-parent-packaging-review.md` without altering the original report or its source/hash provenance.

The proposed P-CONTROL-1 getter clause said “preserves account map, created accounts and full substate”. The **full-substate claim is too strong and is withdrawn**. The actual `GetterInversion.ReadOnly` predicate guarantees:

- equality of created-account sets;
- equality of account-map lookup observations at every address;
- equality of log series;
- actual value equal to zero.

It does not claim equality of all substate fields. Access bookkeeping may change during an otherwise read-only getter. Likewise the review's mapping from GetterInversion to “full substate” must not be used as proof of such equality. Whole-journal substate rollback remains correct for an actual failed Θ call, which is a different statement.

The corrected getter proposal is: “On actual successful empty ordinary user input, actual value is zero; output is exactly the mathematical fee's 32-byte representation; created accounts, all account observations and log series are preserved. Access bookkeeping is not required to be unchanged.”

This correction matches the agreed no-write/no-log/pointer-preservation behavior and the existing Lean interface. Root's DirectControl already states that distinction. DirectDrain uses only the guaranteed account/storage observation equality.
